/*
 * Copyright (C) 2017, The Linux Foundation. All rights reserved.
 * Not a Contribution.
 */
/*
 * Copyright (C) 2016 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.bluetooth.avrcp;

import android.annotation.NonNull;
import android.annotation.Nullable;
import android.bluetooth.BluetoothA2dp;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothAvrcp;
import android.bluetooth.BluetoothDevice;
import android.content.BroadcastReceiver;
import com.android.bluetooth.a2dp.A2dpService;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.PackageManager.NameNotFoundException;
import android.content.pm.ResolveInfo;
import android.content.res.Resources;
import android.content.SharedPreferences;
import android.media.AudioManager;
import android.media.MediaDescription;
import android.media.MediaMetadata;
import android.media.browse.MediaBrowser;
import android.media.session.MediaSession;
import android.media.session.MediaSession.QueueItem;
import android.media.session.MediaSessionManager;
import android.media.session.PlaybackState;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.os.Looper;
import android.os.Message;
import android.os.SystemClock;
import android.os.SystemProperties;
import android.os.UserManager;
import android.util.Log;
import android.view.KeyEvent;
import com.android.bluetooth.Utils;
import android.app.Notification;
import android.app.NotificationManager;

import com.android.bluetooth.btservice.ProfileService;
import com.android.bluetooth.R;
import com.android.bluetooth.Utils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

/******************************************************************************
 * support Bluetooth AVRCP profile. support metadata, play status, event
 * notifications, address player selection and browse feature implementation.
 ******************************************************************************/

public final class Avrcp {
    private static final boolean DEBUG = true;
    private static final String TAG = "Avrcp";
    private static final String ABSOLUTE_VOLUME_BLACKLIST = "absolute_volume_blacklist";
    private static final String AVRCP_VERSION_PROPERTY = "persist.bluetooth.avrcpversion";
    private static final String AVRCP_1_4_STRING = "avrcp14";
    private static final String AVRCP_1_5_STRING = "avrcp15";
    private static final String AVRCP_1_6_STRING = "avrcp16";

    private Context mContext;
    private final AudioManager mAudioManager;
    private AvrcpMessageHandler mHandler;
    private final BluetoothAdapter mAdapter;
    private A2dpService mA2dpService;
    private MediaSessionManager mMediaSessionManager;
    private @Nullable MediaController mMediaController;
    private MediaControllerListener mMediaControllerCb;
    private MediaAttributes mMediaAttributes;
    private long mLastQueueId;
    private PackageManager mPackageManager;
    private int mTransportControlFlags;
    private int mA2dpState;
    private @NonNull PlaybackState mCurrentPlayerState;
    private long mLastStateUpdate;
    private int mPlayStatusChangedNT;
    private int mTrackChangedNT;
    private int mPlayPosChangedNT;
    private long mSongLengthMs;
    private long mPlaybackIntervalMs;
    private long mLastReportedPosition;
    private long mNextPosMs;
    private long mPrevPosMs;
    private int mFeatures;
    private int mRemoteVolume;
    private int mLastRemoteVolume;
    private int mInitialRemoteVolume;
    private BrowsablePlayerListBuilder mBrowsableListBuilder;

    /* Local volume in audio index 0-15 */
    private int mLocalVolume;
    private int mLastLocalVolume;
    private int mAbsVolThreshold;

    private boolean mFastforward;
    private boolean mRewind;
    private boolean mRemotePassthroughCmd;

    private String mAddress;
    private HashMap<Integer, Integer> mVolumeMapping;

    private int mLastDirection;
    private final int mVolumeStep;
    private final int mAudioStreamMax;
    private boolean mVolCmdAdjustInProgress;
    private boolean mVolCmdSetInProgress;
    private int mAbsVolRetryTimes;

    private static final int NO_PLAYER_ID = 0;

    private int mCurrAddrPlayerID;
    private int mCurrBrowsePlayerID;
    private int mLastUsedPlayerID;
    private AvrcpMediaRsp mAvrcpMediaRsp;
    private int maxAvrcpConnections = 1; // Max Avrcp connections at any time
    private static final int INVALID_DEVICE_INDEX = 0xFF;
    private boolean pts_test = false;

    /* UID counter to be shared across different files. */
    static short sUIDCounter;

    /* BTRC features */
    public static final int BTRC_FEAT_METADATA = 0x01;
    public static final int BTRC_FEAT_ABSOLUTE_VOLUME = 0x02;
    public static final int BTRC_FEAT_BROWSE = 0x04;
    public static final int BTRC_FEAT_AVRC_UI_UPDATE = 0x08;

    /* AVRC response codes, from avrc_defs */
    private static final int AVRC_RSP_NOT_IMPL = 8;
    private static final int AVRC_RSP_ACCEPT = 9;
    private static final int AVRC_RSP_REJ = 10;
    private static final int AVRC_RSP_IN_TRANS = 11;
    private static final int AVRC_RSP_IMPL_STBL = 12;
    private static final int AVRC_RSP_CHANGED = 13;
    private static final int AVRC_RSP_INTERIM = 15;

    /* AVRC request commands from Native */
    private static final int MSG_NATIVE_REQ_GET_RC_FEATURES = 1;
    private static final int MSG_NATIVE_REQ_GET_PLAY_STATUS = 2;
    private static final int MSG_NATIVE_REQ_GET_ELEM_ATTRS = 3;
    private static final int MSG_NATIVE_REQ_REGISTER_NOTIFICATION = 4;
    private static final int MSG_NATIVE_REQ_VOLUME_CHANGE = 5;
    private static final int MSG_NATIVE_REQ_GET_FOLDER_ITEMS = 6;
    private static final int MSG_NATIVE_REQ_SET_ADDR_PLAYER = 7;
    private static final int MSG_NATIVE_REQ_SET_BR_PLAYER = 8;
    private static final int MSG_NATIVE_REQ_CHANGE_PATH = 9;
    private static final int MSG_NATIVE_REQ_PLAY_ITEM = 10;
    private static final int MSG_NATIVE_REQ_GET_ITEM_ATTR = 11;
    private static final int MSG_NATIVE_REQ_GET_TOTAL_NUM_OF_ITEMS = 12;
    private static final int MSG_NATIVE_REQ_PASS_THROUGH = 13;

    /* other AVRC messages */
    private static final int MSG_PLAY_INTERVAL_TIMEOUT = 14;
    private static final int MSG_ADJUST_VOLUME = 15;
    private static final int MSG_SET_ABSOLUTE_VOLUME = 16;
    private static final int MSG_ABS_VOL_TIMEOUT = 17;
    private static final int MSG_FAST_FORWARD = 18;
    private static final int MSG_REWIND = 19;
    private static final int MSG_SET_A2DP_AUDIO_STATE = 20;
    private static final int MSG_ADDRESSED_PLAYER_CHANGED_RSP = 21;
    private static final int MSG_AVAILABLE_PLAYERS_CHANGED_RSP = 22;
    private static final int MSG_NOW_PLAYING_CHANGED_RSP = 23;
    private static final int MESSAGE_DEVICE_RC_CLEANUP = 24;

    private static final int STACK_CLEANUP = 0;
    private static final int APP_CLEANUP = 1;
    private static final int CMD_TIMEOUT_DELAY = 2000;
    private static final int MAX_ERROR_RETRY_TIMES = 6;
    private static final int AVRCP_MAX_VOL = 127;
    private static final int AVRCP_BASE_VOLUME_STEP = 1;
    public static final int AVRC_ID_VOL_UP = 0x41;
    public static final int AVRC_ID_VOL_DOWN = 0x42;

    /* Communicates with MediaPlayer to fetch media content */
    private BrowsedMediaPlayer mBrowsedMediaPlayer;

    /* Addressed player handling */
    private AddressedMediaPlayer mAddressedMediaPlayer;

    /* List of Media player instances, useful for retrieving MediaPlayerList or MediaPlayerInfo */
    private SortedMap<Integer, MediaPlayerInfo> mMediaPlayerInfoList;

    /* List of media players which supports browse */
    private List<BrowsePlayerInfo> mBrowsePlayerInfoList;

    /* Manage browsed players */
    private AvrcpBrowseManager mAvrcpBrowseManager;

    /* BIP Responder */
    static private AvrcpBipRsp mAvrcpBipRsp;

    /* Broadcast receiver for device connections intent broadcasts */
    private final BroadcastReceiver mAvrcpReceiver = new AvrcpServiceBroadcastReceiver();
    private final BroadcastReceiver mBootReceiver = new AvrcpServiceBootReceiver();

    /* Recording passthrough key dispatches */
    static private final int PASSTHROUGH_LOG_MAX_SIZE = DEBUG ? 50 : 10;
    private EvictingQueue<MediaKeyLog> mPassthroughLogs; // Passthorugh keys dispatched
    private List<MediaKeyLog> mPassthroughPending; // Passthrough keys sent not dispatched yet
    private int mPassthroughDispatched; // Number of keys dispatched

    private class MediaKeyLog {
        private long mTimeSent;
        private long mTimeProcessed;
        private String mPackage;
        private KeyEvent mEvent;

        public MediaKeyLog(long time, KeyEvent event) {
            mEvent = event;
            mTimeSent = time;
        }

        public boolean addDispatch(long time, KeyEvent event, String packageName) {
            if (mPackage != null) return false;
            if (event.getAction() != mEvent.getAction()) return false;
            if (event.getKeyCode() != mEvent.getKeyCode()) return false;
            mPackage = packageName;
            mTimeProcessed = time;
            return true;
        }

        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append(android.text.format.DateFormat.format("MM-dd HH:mm:ss", mTimeSent));
            sb.append(" " + mEvent.toString());
            if (mPackage == null) {
                sb.append(" (undispatched)");
            } else {
                sb.append(" to " + mPackage);
                sb.append(" in " + (mTimeProcessed - mTimeSent) + "ms");
            }
            return sb.toString();
        }
    }

    // Device dependent registered Notification & Variables
    private class DeviceDependentFeature {
        private Context mContext;
        private BluetoothDevice mCurrentDevice;
        private @NonNull PlaybackState mCurrentPlayState;
        private int mPlayStatusChangedNT;
        private int mNowPlayingChangedNT;
        private int mTrackChangedNT;
        private long mNextPosMs;
        private long mPrevPosMs;
        private long mPlaybackIntervalMs;
        private long mLastReportedPosition;
        private int mPlayPosChangedNT;
        private int mFeatures;
        private int mLastDirection;
        private int mAbsoluteVolume;
        private int mLastSetVolume;
        private boolean mVolCmdSetInProgress;
        private boolean mVolCmdAdjustInProgress;
        private boolean isAbsoluteVolumeSupportingDevice;
        private int mAbsVolRetryTimes;
        private int keyPressState;
        private long mTracksPlayed;
        private int mAvailablePlayersChangedNT;

        private int mRemoteVolume;
        private int mLastRemoteVolume;
        private int mInitialRemoteVolume;
        private boolean isActiveDevice;

        /* Local volume in audio index 0-15 */
        private int mLocalVolume;
        private int mLastLocalVolume;
        private int mAbsVolThreshold;
        private HashMap<Integer, Integer> mVolumeMapping;

        public DeviceDependentFeature(Context context) {
            mContext = context;
            mCurrentDevice = null;
            mCurrentPlayState = new PlaybackState.Builder().setState(PlaybackState.STATE_NONE, -1L, 0.0f).build();;
            mPlayStatusChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
            mNowPlayingChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
            mTrackChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
            mNextPosMs = -1;
            mPrevPosMs = -1;
            mPlaybackIntervalMs = 0L;
            mLastReportedPosition = -1;
            mPlayPosChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
            mFeatures = 0;
            mLastDirection = 0;
            mTracksPlayed = 0;
            mVolCmdAdjustInProgress = false;
            mVolCmdSetInProgress = false;
            isAbsoluteVolumeSupportingDevice = false;
            mAbsVolRetryTimes = 0;
            keyPressState = AvrcpConstants.KEY_STATE_RELEASE; //Key release state
            mRemoteVolume = -1;
            mAvailablePlayersChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
            mInitialRemoteVolume = -1;
            isActiveDevice = false;
            mLastRemoteVolume = -1;
            mLocalVolume = -1;
            mLastLocalVolume = -1;
            mAbsVolThreshold = 0;
            mVolumeMapping = new HashMap<Integer, Integer>();
            Resources resources = context.getResources();
            if (resources != null) {
                mAbsVolThreshold = resources.getInteger(R.integer.a2dp_absolute_volume_initial_threshold);
            }
        }
    };
    DeviceDependentFeature[] deviceFeatures;

    static {
        classInitNative();
    }


    private Avrcp(Context context, A2dpService svc, int maxConnections ) {
        if (DEBUG) Log.v(TAG, "Avrcp");
        mAdapter = BluetoothAdapter.getDefaultAdapter();
        mMediaAttributes = new MediaAttributes(null);
        mLastQueueId = MediaSession.QueueItem.UNKNOWN_ID;
        mCurrentPlayerState = new PlaybackState.Builder().setState(PlaybackState.STATE_NONE, -1L, 0.0f).build();
        mA2dpState = BluetoothA2dp.STATE_NOT_PLAYING;
        mLastStateUpdate = -1L;
        mSongLengthMs = 0L;
        sUIDCounter = AvrcpConstants.DEFAULT_UID_COUNTER;
        mCurrAddrPlayerID = NO_PLAYER_ID;
        mCurrBrowsePlayerID = 0;
        mContext = context;
        mLastUsedPlayerID = 0;
        mAddressedMediaPlayer = null;
        mAvrcpBipRsp = null;
        mA2dpService = svc;
        maxAvrcpConnections = maxConnections;
        deviceFeatures = new DeviceDependentFeature[maxAvrcpConnections];
        for(int i = 0; i < maxAvrcpConnections; i++) {
            deviceFeatures[i] = new DeviceDependentFeature(mContext);
        }
        mFastforward = false;
        mRewind = false;
        mRemotePassthroughCmd = false;

        initNative(maxAvrcpConnections);

        mMediaSessionManager = (MediaSessionManager) context.getSystemService(
            Context.MEDIA_SESSION_SERVICE);
        mAudioManager = (AudioManager) context.getSystemService(Context.AUDIO_SERVICE);
        mAudioStreamMax = mAudioManager.getStreamMaxVolume(AudioManager.STREAM_MUSIC);
        mVolumeStep = Math.max(AVRCP_BASE_VOLUME_STEP, AVRCP_MAX_VOL/mAudioStreamMax);

        mBrowsableListBuilder = new BrowsablePlayerListBuilder();
        // Register for package removal intent broadcasts for media button receiver persistence
        IntentFilter pkgFilter = new IntentFilter();
        pkgFilter.addAction(Intent.ACTION_PACKAGE_REMOVED);
        pkgFilter.addAction(Intent.ACTION_PACKAGE_ADDED);
        pkgFilter.addAction(Intent.ACTION_PACKAGE_CHANGED);
        pkgFilter.addAction(Intent.ACTION_PACKAGE_DATA_CLEARED);
        pkgFilter.addDataScheme("package");
        context.registerReceiver(mAvrcpReceiver, pkgFilter);

        IntentFilter bootFilter = new IntentFilter();
        bootFilter.addAction(Intent.ACTION_BOOT_COMPLETED);
        context.registerReceiver(mBootReceiver, bootFilter);
    }

    private void start() {
        if (DEBUG) Log.v(TAG, "start");
        HandlerThread thread = new HandlerThread("BluetoothAvrcpHandler");
        thread.start();
        Looper looper = thread.getLooper();
        mHandler = new AvrcpMessageHandler(looper);
        mMediaControllerCb = new MediaControllerListener();
        mAvrcpMediaRsp = new AvrcpMediaRsp();
        mMediaPlayerInfoList = new TreeMap<Integer, MediaPlayerInfo>();
        mBrowsePlayerInfoList = Collections.synchronizedList(new ArrayList<BrowsePlayerInfo>());
        mPassthroughDispatched = 0;
        mPassthroughLogs = new EvictingQueue<MediaKeyLog>(PASSTHROUGH_LOG_MAX_SIZE);
        mPassthroughPending = Collections.synchronizedList(new ArrayList<MediaKeyLog>());
        if (mMediaSessionManager != null) {
            mMediaSessionManager.addOnActiveSessionsChangedListener(mActiveSessionListener, null,
                    mHandler);
            mMediaSessionManager.setCallback(mButtonDispatchCallback, null);
        }
        mPackageManager = mContext.getApplicationContext().getPackageManager();

        boolean isCoverArtSupported = mContext.getResources().getBoolean
                (R.bool.avrcp_coverart_support);
        if (DEBUG) Log.d(TAG, "isCoverArtSupported: " + isCoverArtSupported);
        String avrcpVersion = SystemProperties.get(AVRCP_VERSION_PROPERTY, AVRCP_1_4_STRING);
        if (DEBUG) Log.d(TAG, "avrcpVersion: " + avrcpVersion);
        /* Enable Cover Art support is version is 1.6 and flag is set in config */
        if (isCoverArtSupported && avrcpVersion != null &&
            avrcpVersion.equals(AVRCP_1_6_STRING))
            mAvrcpBipRsp = new AvrcpBipRsp(mContext);
        if (mAvrcpBipRsp != null) {
            if (DEBUG) Log.d(TAG, "Starting AVRCP BIP Responder Service");
            mAvrcpBipRsp.start();
        }
        /* create object to communicate with addressed player */
        mAddressedMediaPlayer = new AddressedMediaPlayer(mAvrcpMediaRsp);

        /* initialize BrowseMananger which manages Browse commands and response */
        mAvrcpBrowseManager = new AvrcpBrowseManager(mContext, mAvrcpMediaRsp);

        initMediaPlayersList();

        UserManager manager = UserManager.get(mContext);
        if (manager == null || manager.isUserUnlocked()) {
            if (DEBUG) Log.d(TAG, "User already unlocked, initializing player lists");
            // initialize browsable player list and build media player list
            mBrowsableListBuilder.start();
        }
    }

    public static Avrcp make(Context context, A2dpService svc,
                             int maxConnections) {
        if (DEBUG) Log.v(TAG, "make");
        Avrcp ar = new Avrcp(context, svc, maxConnections);
        ar.start();
        return ar;
    }

    public void doQuit() {
        if (DEBUG) Log.d(TAG, "doQuit");
        synchronized (this) {
            if (mMediaController != null) mMediaController.unregisterCallback(mMediaControllerCb);
        }
        if (mMediaSessionManager != null) {
            mMediaSessionManager.setCallback(null, null);
            mMediaSessionManager.removeOnActiveSessionsChangedListener(mActiveSessionListener);
        }

        mHandler.removeCallbacksAndMessages(null);
        Looper looper = mHandler.getLooper();
        if (looper != null) {
            looper.quit();
        }

        if (mAvrcpBipRsp != null) {
            mAvrcpBipRsp.stop();
            mAvrcpBipRsp = null;
        }
        mHandler = null;
        mContext.unregisterReceiver(mAvrcpReceiver);
        mContext.unregisterReceiver(mBootReceiver);

        mBrowsableListBuilder.cleanup();
        mAddressedMediaPlayer.cleanup();
        mAvrcpBrowseManager.cleanup();
    }

    public void clearDeviceDependentFeature() {
        Log.d(TAG, "Enter clearDeviceDependentFeature()");
        for (int i = 0; i < maxAvrcpConnections; i++) {
            deviceFeatures[i].keyPressState =
                AvrcpConstants.KEY_STATE_RELEASE; //Key release state
            if (deviceFeatures[i].mVolumeMapping != null)
                deviceFeatures[i].mVolumeMapping.clear();
        }
        Log.d(TAG, "Exit clearDeviceDependentFeature()");
    }

    public void cleanup() {
        if (DEBUG) Log.d(TAG, "cleanup");
        cleanupNative();
        if (mVolumeMapping != null)
            mVolumeMapping.clear();
    }

    private class MediaControllerListener extends MediaController.Callback {
        @Override
        public void onMetadataChanged(MediaMetadata metadata) {
            if (DEBUG) Log.v(TAG, "onMetadataChanged");
            updateCurrentMediaState(false, null);
        }
        @Override
        public synchronized void onPlaybackStateChanged(PlaybackState state) {
            if (DEBUG) Log.v(TAG, "onPlaybackStateChanged: state " + state.toString());
            updateCurrentMediaState(false, null);
        }

        @Override
        public void onSessionDestroyed() {
            Log.v(TAG, "MediaController session destroyed");
            synchronized (Avrcp.this) {
                if (mMediaController != null)
                    removeMediaController(mMediaController.getWrappedInstance());
            }
        }


        @Override
        public void onQueueChanged(List<MediaSession.QueueItem> queue) {
            if (queue == null) {
                Log.v(TAG, "onQueueChanged: received null queue");
                return;
            }

            Log.v(TAG, "onQueueChanged: NowPlaying list changed, Queue Size = "+ queue.size());
            mHandler.sendEmptyMessage(MSG_NOW_PLAYING_CHANGED_RSP);
        }
    }

    /** Handles Avrcp messages. */
    private final class AvrcpMessageHandler extends Handler {
        private AvrcpMessageHandler(Looper looper) {
            super(looper);
        }

        @Override
        public void handleMessage(Message msg) {
            int deviceIndex  = INVALID_DEVICE_INDEX;
            if (DEBUG) Log.v(TAG, "AvrcpMessageHandler: received message=" + msg.what);

            switch (msg.what) {
            case MSG_NATIVE_REQ_GET_RC_FEATURES:
            {
                String address = (String) msg.obj;
                if (DEBUG)
                    Log.v(TAG, "MSG_GET_RC_FEATURES: address="+address+
                            ", features="+msg.arg1);
                BluetoothDevice device = mAdapter.getRemoteDevice(address);
                deviceIndex = getIndexForDevice(device);
                if (deviceIndex == INVALID_DEVICE_INDEX) {
                    Log.v(TAG,"device entry not present, bailing out");
                    return;
                }
                deviceFeatures[deviceIndex].mFeatures = msg.arg1;
                deviceFeatures[deviceIndex].mFeatures =
                    modifyRcFeatureFromBlacklist(deviceFeatures[deviceIndex].mFeatures,
                    address);
                Log.d(TAG, "avrcpct-passthrough pts_test = " + pts_test);
                if (pts_test) {
                    Log.v(TAG,"fake BTRC_FEAT_ABSOLUTE_VOLUME remote feat support for pts test");
                    deviceFeatures[deviceIndex].mFeatures =
                                 deviceFeatures[deviceIndex].mFeatures | BTRC_FEAT_ABSOLUTE_VOLUME;
                }
                deviceFeatures[deviceIndex].isAbsoluteVolumeSupportingDevice =
                        ((deviceFeatures[deviceIndex].mFeatures &
                        BTRC_FEAT_ABSOLUTE_VOLUME) != 0);
                mAudioManager.avrcpSupportsAbsoluteVolume(device.getAddress(),
                        isAbsoluteVolumeSupported());
                Log.v(TAG," update audio manager for abs vol state = "
                        + isAbsoluteVolumeSupported());
                deviceFeatures[deviceIndex].mLastLocalVolume = -1;
                deviceFeatures[deviceIndex].mRemoteVolume = -1;
                deviceFeatures[deviceIndex].mLocalVolume = -1;
                deviceFeatures[deviceIndex].mInitialRemoteVolume = -1;
                if (deviceFeatures[deviceIndex].mVolumeMapping != null)
                    deviceFeatures[deviceIndex].mVolumeMapping.clear();

                if ((deviceFeatures[deviceIndex].mFeatures &
                        BTRC_FEAT_AVRC_UI_UPDATE) != 0)
                {
                    int NOTIFICATION_ID = android.R.drawable.stat_sys_data_bluetooth;
                    Notification notification = new Notification.Builder(mContext)
                        .setContentTitle("Bluetooth Media Browsing")
                        .setContentText("Peer supports advanced feature")
                        .setSubText("Re-pair from peer to enable it")
                        .setSmallIcon(android.R.drawable.stat_sys_data_bluetooth)
                        .setDefaults(Notification.DEFAULT_ALL)
                        .build();
                    NotificationManager manager = (NotificationManager)
                        mContext.getSystemService(Context.NOTIFICATION_SERVICE);
                    manager.notify(NOTIFICATION_ID, notification);
                    Log.v(TAG," update notification manager on remote repair request");
                }
                break;
            }

            case MSG_NATIVE_REQ_GET_PLAY_STATUS:
            {
                BluetoothDevice device;
                int playState = PLAYSTATUS_ERROR;
                int position;

                String address = Utils.getAddressStringFromByte((byte[]) msg.obj);
                Log.v(TAG, "Event for device address " + address);

                device = mAdapter.getRemoteDevice(address);
                deviceIndex = getIndexForDevice(device);
                if (deviceIndex == INVALID_DEVICE_INDEX) {
                    Log.e(TAG,"Invalid device index for play status");
                    break;
                }
                playState = convertPlayStateToPlayStatus(deviceFeatures[deviceIndex].mCurrentPlayState);
                if (mFastforward) {
                    playState = PLAYSTATUS_FWD_SEEK;
                }
                if (mRewind) {
                    playState = PLAYSTATUS_REV_SEEK;
                }
                if (!mFastforward && !mRewind) {
                    playState = convertPlayStateToPlayStatus(deviceFeatures[deviceIndex].mCurrentPlayState);
                }
                position = (int)getPlayPosition(device);
                if (DEBUG)
                    Log.v(TAG, "Play Status for : " + device.getName() +
                          " state: " + playState + " position: " + position);
                if (position == -1) {
                    Log.v(TAG, "Force play postion to 0, for getPlayStatus Rsp");
                    position = 0;
                }

                getPlayStatusRspNative(getByteAddress(device), playState, (int)mSongLengthMs, position);
                break;
            }

            case MSG_NATIVE_REQ_GET_ELEM_ATTRS:
            {
                String[] textArray;
                AvrcpCmd.ElementAttrCmd elem = (AvrcpCmd.ElementAttrCmd) msg.obj;
                byte numAttr = elem.mNumAttr;
                int[] attrIds = elem.mAttrIDs;
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_GET_ELEM_ATTRS:numAttr=" + numAttr);
                textArray = new String[numAttr];
                StringBuilder responseDebug = new StringBuilder();
                responseDebug.append("getElementAttr response: ");
                for (int i = 0; i < numAttr; ++i) {
                    textArray[i] = mMediaAttributes.getString(attrIds[i]);
                    responseDebug.append("[" + attrIds[i] + "=" + textArray[i] + "] ");
                }
                Log.v(TAG, responseDebug.toString());
                byte[] bdaddr = elem.mAddress;
                getElementAttrRspNative(bdaddr, numAttr, attrIds, textArray);
                break;
            }

            case MSG_NATIVE_REQ_REGISTER_NOTIFICATION:
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_REGISTER_NOTIFICATION:event=" + msg.arg1 +
                        " param=" + msg.arg2);
                processRegisterNotification((byte[]) msg.obj, msg.arg1, msg.arg2);
                break;

            case MSG_AVAILABLE_PLAYERS_CHANGED_RSP: {
                if (DEBUG) Log.v(TAG, "MSG_AVAILABLE_PLAYERS_CHANGED_RSP");
                removeMessages(MSG_AVAILABLE_PLAYERS_CHANGED_RSP);
                for (int i = 0; i < maxAvrcpConnections; i++) {
                    if (deviceFeatures[i].mCurrentDevice != null) {
                        registerNotificationRspAvalPlayerChangedNative(
                            AvrcpConstants.NOTIFICATION_TYPE_CHANGED,
                            getByteAddress(deviceFeatures[i].mCurrentDevice));
                    }
                }
            }   break;

            case MSG_NOW_PLAYING_CHANGED_RSP: {
                if (DEBUG) Log.v(TAG, "MSG_NOW_PLAYING_CHANGED_RSP");
                removeMessages(MSG_NOW_PLAYING_CHANGED_RSP);
                mAddressedMediaPlayer.updateNowPlayingList(mMediaController);
            }   break;

            case MSG_ADDRESSED_PLAYER_CHANGED_RSP:
                // Later addressed players override earlier ones.
                if (hasMessages(MSG_ADDRESSED_PLAYER_CHANGED_RSP)) {
                    Log.i(TAG, "MSG_ADDRESSED_PLAYER_CHANGED_RSP: skip, more changes in queue");
                    break;
                }
                if (DEBUG)
                    Log.v(TAG, "MSG_ADDRESSED_PLAYER_CHANGED_RSP: newAddrPlayer = " + msg.arg1);
                for (int i = 0; i < maxAvrcpConnections; i++) {
                    if (deviceFeatures[i].mCurrentDevice != null) {
                        registerNotificationRspAddrPlayerChangedNative(
                            AvrcpConstants.NOTIFICATION_TYPE_CHANGED, msg.arg1, sUIDCounter,
                            getByteAddress(deviceFeatures[i].mCurrentDevice));
                    }
                } 
                break;

            case MSG_PLAY_INTERVAL_TIMEOUT:
                if (DEBUG) Log.v(TAG, "MSG_PLAY_INTERVAL_TIMEOUT");
                Log.v(TAG, "event for device address " + (BluetoothDevice)msg.obj);
                deviceIndex = getIndexForDevice((BluetoothDevice) msg.obj);
                if (deviceIndex == INVALID_DEVICE_INDEX) {
                    Log.e(TAG,"invalid index for device");
                    break;
                }
                sendPlayPosNotificationRsp(false, deviceIndex);
                break;

            case MSG_NATIVE_REQ_VOLUME_CHANGE: {
                if (!isAbsoluteVolumeSupported()) {
                    if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_VOLUME_CHANGE ignored, not supported");
                    break;
                }
                byte absVol = (byte) ((byte) msg.arg1 & 0x7f); // discard MSB as it is RFD
                if (DEBUG)
                    Log.v(TAG, "MSG_NATIVE_REQ_VOLUME_CHANGE: volume=" + absVol + " ctype="
                                    + msg.arg2);
                Bundle data = msg.getData();
                byte[] bdaddr = data.getByteArray("BdAddress");
                String address = Utils.getAddressStringFromByte(bdaddr);
                Log.v(TAG, "event for device address " + address);
                deviceIndex = getIndexForDevice(mAdapter.getRemoteDevice(address));
                if (deviceIndex == INVALID_DEVICE_INDEX) {
                    Log.e(TAG,"invalid index for device");
                    break;
                }
                boolean volAdj = false;
                if (msg.arg2 == AVRC_RSP_ACCEPT || msg.arg2 == AVRC_RSP_REJ) {
                    if (mVolCmdAdjustInProgress == false && mVolCmdSetInProgress == false) {
                        Log.e(TAG, "Unsolicited response, ignored");
                        break;
                    }
                    removeMessages(MSG_ABS_VOL_TIMEOUT);

                    volAdj = mVolCmdAdjustInProgress;
                    mVolCmdAdjustInProgress = false;
                    mVolCmdSetInProgress = false;
                    mAbsVolRetryTimes = 0;
                }

                // convert remote volume to local volume
                int volIndex = convertToAudioStreamVolume(absVol);
                if (DEBUG) Log.v(TAG,"Volume Index = " + volIndex);
                if (deviceFeatures[deviceIndex].mInitialRemoteVolume == -1) {
                    deviceFeatures[deviceIndex].mInitialRemoteVolume = absVol;
                    if (deviceFeatures[deviceIndex].mAbsVolThreshold > 0 &&
                        deviceFeatures[deviceIndex].mAbsVolThreshold <
                        mAudioStreamMax &&
                        volIndex > deviceFeatures[deviceIndex].mAbsVolThreshold) {
                        if (DEBUG) Log.v(TAG, "remote inital volume too high " + volIndex + ">" +
                            deviceFeatures[deviceIndex].mAbsVolThreshold);
                        Message msg1 = mHandler.obtainMessage(MSG_SET_ABSOLUTE_VOLUME,
                            deviceFeatures[deviceIndex].mAbsVolThreshold , 0);
                        mHandler.sendMessage(msg1);
                        deviceFeatures[deviceIndex].mRemoteVolume = absVol;
                        deviceFeatures[deviceIndex].mLocalVolume = volIndex;
                        break;
                    }
                }
                if (deviceFeatures[deviceIndex].mLocalVolume != volIndex &&
                                                (msg.arg2 == AVRC_RSP_ACCEPT ||
                                                 msg.arg2 == AVRC_RSP_CHANGED ||
                                                 msg.arg2 == AVRC_RSP_INTERIM)) {
                    /* If the volume has successfully changed */
                    if (!deviceFeatures[deviceIndex].isActiveDevice &&
                           (msg.arg2 == AVRC_RSP_CHANGED || msg.arg2 == AVRC_RSP_INTERIM)) {
                        Log.d(TAG, "Do not change volume from an inactive device");
                        break;
                    }

                    deviceFeatures[deviceIndex].mLocalVolume = volIndex;
                    if (deviceFeatures[deviceIndex].mLastLocalVolume != -1
                        && msg.arg2 == AVRC_RSP_ACCEPT) {
                        if (deviceFeatures[deviceIndex].mLastLocalVolume != volIndex) {
                            /* remote volume changed more than requested due to
                             * local and remote has different volume steps */
                            if (DEBUG) Log.d(TAG, "Remote returned volume does not match desired volume "
                                + deviceFeatures[deviceIndex].mLastLocalVolume + " vs "
                                + volIndex);
                            deviceFeatures[deviceIndex].mLastLocalVolume =
                                deviceFeatures[deviceIndex].mLocalVolume;
                        }
                    }
                    // remember the remote volume value, as it's the one supported by remote
                    if (volAdj) {
                        synchronized (deviceFeatures[deviceIndex].mVolumeMapping) {
                            deviceFeatures[deviceIndex].mVolumeMapping.put(volIndex, (int)absVol);
                            if (DEBUG) Log.v(TAG, "remember volume mapping " +volIndex+ "-"+absVol);
                        }
                    }
                    notifyVolumeChanged(deviceFeatures[deviceIndex].mLocalVolume);
                    deviceFeatures[deviceIndex].mRemoteVolume = absVol;
                    long pecentVolChanged = ((long)absVol * 100) / 0x7f;
                    Log.e(TAG, "percent volume changed: " + pecentVolChanged + "%");
                } else if (msg.arg2 == AVRC_RSP_REJ) {
                    Log.e(TAG, "setAbsoluteVolume call rejected");
                } else if (volAdj && deviceFeatures[deviceIndex].mLastRemoteVolume > 0
                            && deviceFeatures[deviceIndex].mLastRemoteVolume < AVRCP_MAX_VOL &&
                            deviceFeatures[deviceIndex].mLocalVolume == volIndex &&
                            (msg.arg2 == AVRC_RSP_ACCEPT )) {
                    /* oops, the volume is still same, remote does not like the value
                     * retry a volume one step up/down */
                    if (DEBUG) Log.d(TAG, "Remote device didn't tune volume, let's try one more step.");
                    int retry_volume = Math.min(AVRCP_MAX_VOL,
                            Math.max(0, deviceFeatures[deviceIndex].mLastRemoteVolume +
                                        deviceFeatures[deviceIndex].mLastDirection));
                    if (setVolumeNative(retry_volume,
                            getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice))) {
                        deviceFeatures[deviceIndex].mLastRemoteVolume = retry_volume;
                        sendMessageDelayed(obtainMessage(MSG_ABS_VOL_TIMEOUT,
                            0, 0, deviceFeatures[deviceIndex].mCurrentDevice), CMD_TIMEOUT_DELAY);
                        deviceFeatures[deviceIndex].mVolCmdAdjustInProgress = true;
                    }
                } else if (msg.arg2 == AVRC_RSP_REJ) {
                    if (DEBUG)
                        Log.v(TAG, "setAbsoluteVolume call rejected");
                }
            }   break;

            case MSG_ADJUST_VOLUME:
            {
                if (!isAbsoluteVolumeSupported()) {
                    if (DEBUG) Log.v(TAG, "ignore MSG_ADJUST_VOLUME");
                    break;
                }

                if (mA2dpService.isMulticastFeatureEnabled() &&
                        areMultipleDevicesConnected()) {
                    if (DEBUG) Log.v(TAG, "Volume change not entertained as multicast is enabled & multiple devices are connected");
                    break;
                }

                if (DEBUG) Log.d(TAG, "MSG_ADJUST_VOLUME: direction=" + msg.arg1);
                for (int i = 0; i < maxAvrcpConnections; i++) {
                    if (deviceFeatures[i].mCurrentDevice != null &&
                            deviceFeatures[i].isActiveDevice) {
                          deviceIndex = i;
                          if ((deviceFeatures[deviceIndex].mVolCmdAdjustInProgress) ||
                                (deviceFeatures[deviceIndex].mVolCmdSetInProgress)){
                          if (DEBUG)
                               Log.w(TAG, "already a volume command in progress" +
                                       "for this device.");
                              continue;
                          }
                          if (deviceFeatures[deviceIndex].mInitialRemoteVolume == -1) {
                              if (DEBUG) Log.d(TAG, "remote never tell us initial volume, black list it.");
                              blackListCurrentDevice(deviceIndex);
                              break;
                          }
                              // Wait on verification on volume from device, before changing the volume.
                          if (deviceFeatures[deviceIndex].mRemoteVolume != -1 &&
                                   (msg.arg1 == -1 || msg.arg1 == 1)) {
                              int setVol = -1;
                              int targetVolIndex = -1;
                              if (deviceFeatures[deviceIndex].mLocalVolume == 0 && msg.arg1 == -1) {
                                 if (DEBUG) Log.w(TAG, "No need to Vol down from 0.");
                              break;
                              }
                              if (deviceFeatures[deviceIndex].mLocalVolume ==
                                      mAudioStreamMax && msg.arg1 == 1) {
                                  if (DEBUG) Log.w(TAG, "No need to Vol up from max.");
                                  break;
                              }

                              targetVolIndex = deviceFeatures[deviceIndex].mLocalVolume + msg.arg1;
                              if (DEBUG) Log.d(TAG, "Adjusting volume to  " + targetVolIndex);

                              Integer j;
                              synchronized (deviceFeatures[deviceIndex].mVolumeMapping) {
                                  j = deviceFeatures[deviceIndex].mVolumeMapping.get(targetVolIndex);
                           }
                           if (j != null) {
                                /* if we already know this volume mapping, use it */
                               setVol = j.byteValue();
                               if (setVol == deviceFeatures[deviceIndex].mRemoteVolume) {
                                    if (DEBUG) Log.d(TAG, "got same volume from mapping for " +
                                         targetVolIndex + ", ignore.");
                                    setVol = -1;
                               }
                               if (DEBUG) Log.d(TAG, "set volume from mapping " + targetVolIndex + "-" + setVol);
                           }
                           if (setVol == -1) {
                               /* otherwise use phone steps */
                               setVol = Math.min(AVRCP_MAX_VOL,
                                        convertToAvrcpVolume(Math.max(0, targetVolIndex)));
                               if (DEBUG) Log.d(TAG, "set volume from local volume "+ targetVolIndex+"-"+ setVol);
                           }
                           boolean isSetVol = setVolumeNative(setVol ,
                                   getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
                           if (isSetVol) {
                                sendMessageDelayed(obtainMessage(MSG_ABS_VOL_TIMEOUT,
                                    0, 0, deviceFeatures[deviceIndex].mCurrentDevice), CMD_TIMEOUT_DELAY);
                                deviceFeatures[deviceIndex].mVolCmdAdjustInProgress = true;
                                deviceFeatures[deviceIndex].mLastDirection = msg.arg1;
                                deviceFeatures[deviceIndex].mLastRemoteVolume = setVol;
                                deviceFeatures[deviceIndex].mLastLocalVolume = targetVolIndex;
                           } else {
                                if (DEBUG) Log.d(TAG, "adjustVolumeNative failed");
                           }
                        } else {
                             Log.e(TAG, "Unknown direction in MSG_ADJUST_VOLUME");
                        }
                    }
                }
                break;
            }

            case MSG_SET_ABSOLUTE_VOLUME:
            {
                if (!isAbsoluteVolumeSupported()) {
                    if (DEBUG) Log.v(TAG, "ignore MSG_SET_ABSOLUTE_VOLUME");
                    break;
                }

                if (mA2dpService.isMulticastFeatureEnabled() &&
                        areMultipleDevicesConnected()) {
                    if (DEBUG) Log.v(TAG, "Volume change not entertained as multicast is enabled & multiple devices are connected");
                    break;
                }

                if (DEBUG) Log.v(TAG, "MSG_SET_ABSOLUTE_VOLUME");

                int avrcpVolume = convertToAvrcpVolume(msg.arg1);
                avrcpVolume = Math.min(AVRCP_MAX_VOL, Math.max(0, avrcpVolume));
                for (int i = 0; i < maxAvrcpConnections; i++) {
                    if (deviceFeatures[i].mCurrentDevice != null &&
                            deviceFeatures[i].isActiveDevice) {

                          deviceIndex = i;

                          if ((deviceFeatures[deviceIndex].mVolCmdSetInProgress) ||
                                (deviceFeatures[deviceIndex].mVolCmdAdjustInProgress)){
                              if (DEBUG)
                                  Log.w(TAG, "There is already a volume command in progress.");
                              continue;
                          }
                          if (deviceFeatures[deviceIndex].mInitialRemoteVolume == -1) {
                              if (DEBUG) Log.d(TAG, "remote never tell us initial volume, black list it.");
                              blackListCurrentDevice(deviceIndex);
                              break;
                          }
                          Log.v(TAG, "event for device address " + getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
                          boolean isSetVol = setVolumeNative(avrcpVolume ,
                                getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
                          if (isSetVol) {
                              sendMessageDelayed(obtainMessage(MSG_ABS_VOL_TIMEOUT,
                                   0, 0, deviceFeatures[deviceIndex].mCurrentDevice),
                                   CMD_TIMEOUT_DELAY);
                              deviceFeatures[deviceIndex].mVolCmdSetInProgress = true;
                              deviceFeatures[deviceIndex].mLastRemoteVolume = avrcpVolume;
                              deviceFeatures[deviceIndex].mLastLocalVolume = msg.arg1;
                         } else {
                            if (DEBUG) Log.d(TAG, "setVolumeNative failed");
                         }
                    }
                }
                break;
            }
            case MSG_ABS_VOL_TIMEOUT:
                if (DEBUG) Log.v(TAG, "MSG_ABS_VOL_TIMEOUT: Volume change cmd timed out.");
                deviceIndex = getIndexForDevice((BluetoothDevice) msg.obj);
                if (deviceIndex == INVALID_DEVICE_INDEX) {
                    Log.e(TAG,"invalid device index for abs vol timeout");
                    for (int i = 0; i < maxAvrcpConnections; i++) {
                        if (deviceFeatures[i].mVolCmdSetInProgress == true)
                            deviceFeatures[i].mVolCmdSetInProgress = false;
                        if (deviceFeatures[i].mVolCmdAdjustInProgress == true)
                            deviceFeatures[i].mVolCmdAdjustInProgress = false;
                    }
                    break;
                }
                deviceFeatures[deviceIndex].mVolCmdSetInProgress = false;
                deviceFeatures[deviceIndex].mVolCmdAdjustInProgress = false;
                Log.v(TAG, "event for device address " + (BluetoothDevice)msg.obj);
                if (deviceFeatures[deviceIndex].mAbsVolRetryTimes >= MAX_ERROR_RETRY_TIMES) {
                    deviceFeatures[deviceIndex].mAbsVolRetryTimes = 0;
                    blackListCurrentDevice(deviceIndex);
                } else {
                    deviceFeatures[deviceIndex].mAbsVolRetryTimes += 1;
                    boolean isSetVol = setVolumeNative(deviceFeatures[deviceIndex].mLastRemoteVolume ,
                            getByteAddress((BluetoothDevice) msg.obj));
                    if (isSetVol) {
                        sendMessageDelayed(obtainMessage(MSG_ABS_VOL_TIMEOUT,
                                0, 0, msg.obj), CMD_TIMEOUT_DELAY);
                        deviceFeatures[deviceIndex].mVolCmdSetInProgress = true;
                    }
                }
                break;

            case MSG_SET_A2DP_AUDIO_STATE: {
                if (DEBUG) Log.v(TAG, "MSG_SET_A2DP_AUDIO_STATE:" + msg.arg1);
                mA2dpState = msg.arg1;
                BluetoothDevice playStateChangeDevice = (BluetoothDevice)msg.obj;
                Log.v(TAG, "event for device address " + playStateChangeDevice.getAddress());
                deviceIndex = getIndexForDevice(playStateChangeDevice);
                if (deviceIndex == INVALID_DEVICE_INDEX) {
                    Log.e(TAG,"Set A2DP state: invalid index for device");
                    break;
                }
                updateCurrentMediaState(false, (BluetoothDevice)msg.obj);
            }   break;

            case MESSAGE_DEVICE_RC_CLEANUP:
                if (DEBUG)
                    Log.v(TAG,"MESSAGE_DEVICE_RC_CLEANUP: " + msg.arg1);
                if (msg.arg1 == STACK_CLEANUP) {
                    deviceIndex = getIndexForDevice((BluetoothDevice) msg.obj);
                    if (deviceIndex == INVALID_DEVICE_INDEX) {
                        Log.e(TAG,"invalid device index for cleanup");
                        break;
                    }
                    cleanupDeviceFeaturesIndex(deviceIndex);
                } else if (msg.arg1 == APP_CLEANUP) {
                    if (msg.obj == null) {
                        clearDeviceDependentFeature();
                        for (int i = 0; i < maxAvrcpConnections; i++) {
                            cleanupDeviceFeaturesIndex(i);
                        }
                    } else {
                        Log.v(TAG, "Invalid message params");
                        break;
                    }
                } else {
                    Log.v(TAG, "Invalid Arguments to MESSAGE_DEVICE_RC_CLEANUP");
                }
                break;

            case MSG_NATIVE_REQ_GET_FOLDER_ITEMS: {
                AvrcpCmd.FolderItemsCmd folderObj = (AvrcpCmd.FolderItemsCmd) msg.obj;
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_GET_FOLDER_ITEMS " + folderObj);
                switch (folderObj.mScope) {
                    case AvrcpConstants.BTRC_SCOPE_PLAYER_LIST:
                        handleMediaPlayerListRsp(folderObj);
                        break;
                    case AvrcpConstants.BTRC_SCOPE_FILE_SYSTEM:
                    case AvrcpConstants.BTRC_SCOPE_NOW_PLAYING:
                        handleGetFolderItemBrowseResponse(folderObj, folderObj.mAddress);
                        break;
                    default:
                        Log.e(TAG, "unknown scope for getfolderitems. scope = "
                                + folderObj.mScope);
                        getFolderItemsRspNative(folderObj.mAddress,
                                AvrcpConstants.RSP_INV_SCOPE, (short) 0, (byte) 0, 0,
                                null, null, null, null, null, null, null, null);
                }
                break;
            }

            case MSG_NATIVE_REQ_SET_ADDR_PLAYER:
                // object is bdaddr, argument 1 is the selected player id
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_SET_ADDR_PLAYER id=" + msg.arg1);
                setAddressedPlayer((byte[]) msg.obj, msg.arg1);
                break;

            case MSG_NATIVE_REQ_GET_ITEM_ATTR:
                // msg object contains the item attribute object
                AvrcpCmd.ItemAttrCmd cmd = (AvrcpCmd.ItemAttrCmd) msg.obj;
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_GET_ITEM_ATTR " + cmd);
                handleGetItemAttr(cmd);
                break;

            case MSG_NATIVE_REQ_SET_BR_PLAYER:
                // argument 1 is the selected player id
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_SET_BR_PLAYER id=" + msg.arg1);
                setBrowsedPlayer((byte[]) msg.obj, msg.arg1);
                break;

            case MSG_NATIVE_REQ_CHANGE_PATH:
            {
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_CHANGE_PATH");
                Bundle data = msg.getData();
                byte[] bdaddr = data.getByteArray("BdAddress");
                byte[] folderUid = data.getByteArray("folderUid");
                byte direction = data.getByte("direction");
                if (mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr) != null) {
                        mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr).changePath(folderUid,
                        direction);
                } else {
                    Log.e(TAG, "Remote requesting change path before setbrowsedplayer");
                    changePathRspNative(bdaddr, AvrcpConstants.RSP_BAD_CMD, 0);
                }
                break;
            }

            case MSG_NATIVE_REQ_PLAY_ITEM:
            {
                Bundle data = msg.getData();
                byte[] bdaddr = data.getByteArray("BdAddress");
                byte[] uid = data.getByteArray("uid");
                byte scope = data.getByte("scope");
                if (DEBUG)
                    Log.v(TAG, "MSG_NATIVE_REQ_PLAY_ITEM scope=" + scope + " id="
                                    + Utils.byteArrayToString(uid));
                handlePlayItemResponse(bdaddr, uid, scope);
                break;
            }

            case MSG_NATIVE_REQ_GET_TOTAL_NUM_OF_ITEMS:
                if (DEBUG) Log.v(TAG, "MSG_NATIVE_REQ_GET_TOTAL_NUM_OF_ITEMS scope=" + msg.arg1);
                // argument 1 is scope, object is bdaddr
                handleGetTotalNumOfItemsResponse((byte[]) msg.obj, (byte) msg.arg1);
                break;

            case MSG_NATIVE_REQ_PASS_THROUGH:
                if (DEBUG)
                    Log.v(TAG, "MSG_NATIVE_REQ_PASS_THROUGH: id=" + msg.arg1 + " st=" + msg.arg2);
                // argument 1 is id, argument 2 is keyState
                handlePassthroughCmd(msg.arg1, msg.arg2);
                break;

            default:
                Log.e(TAG, "unknown message! msg.what=" + msg.what);
                break;
            }
        }
    }

    private void updatePlayStatusForDevice(int deviceIndex, PlaybackState state) {
        if (state == null) {
            Log.i(TAG,"updatePlayStatusForDevice: device: state is =" + state);
            return;
        }
        Log.i(TAG,"updatePlayStatusForDevice: device: " +
                    deviceFeatures[deviceIndex].mCurrentDevice);

        byte stateBytes = (byte) convertPlayStateToBytes(state.getState());

        /* updating play status in global media player list */
        MediaPlayerInfo player = getAddressedPlayerInfo();
        if (player != null) {
            player.setPlayStatus(stateBytes);
        } else {
            Log.w(TAG, "onPlaybackStateChanged: no addressed player id=" + mCurrAddrPlayerID);
        }

        int newPlayStatus = convertPlayStateToPlayStatus(state);
        int oldPlayStatus = convertPlayStateToPlayStatus(deviceFeatures[deviceIndex].mCurrentPlayState);

        if (mFastforward) {
            newPlayStatus = PLAYSTATUS_FWD_SEEK;
        }
        if (mRewind) {
            newPlayStatus = PLAYSTATUS_REV_SEEK;
        }
        if (DEBUG) {
            Log.v(TAG, "updatePlaybackState (" + deviceFeatures[deviceIndex].mPlayStatusChangedNT + "): "+
                       "old=" + deviceFeatures[deviceIndex].mCurrentPlayState + "(" + oldPlayStatus + "), "+
                       "new=" + state + "(" + newPlayStatus + ")");
        }

        deviceFeatures[deviceIndex].mCurrentPlayState = state;

        if ((deviceFeatures[deviceIndex].mPlayStatusChangedNT ==
                AvrcpConstants.NOTIFICATION_TYPE_INTERIM) &&
               (oldPlayStatus != newPlayStatus) && deviceFeatures[deviceIndex].mCurrentDevice != null) {
            deviceFeatures[deviceIndex].mPlayStatusChangedNT =
                AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
            registerNotificationRspPlayStatusNative(
                    deviceFeatures[deviceIndex].mPlayStatusChangedNT,
                    newPlayStatus,
                    getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
        }
    }

    private boolean isPlayStateToBeUpdated(int deviceIndex) {
        Log.v(TAG, "isPlayStateTobeUpdated: device: "  +
                    deviceFeatures[deviceIndex].mCurrentDevice);
        if (maxAvrcpConnections < 2) {
            Log.v(TAG, "maxAvrcpConnections: " + maxAvrcpConnections);
            return true;
        } else if(mA2dpService.isMulticastFeatureEnabled()) {
            if (!areMultipleDevicesConnected()) {
                Log.v(TAG, "Single connection exists");
                return true;
            } else if (mA2dpService.isMulticastEnabled()) {
                Log.v(TAG, "Multicast is Enabled");
                return true;
            } else {
                Log.v(TAG, "Multiple connection exists, Multicast not enabled");
                if(isDeviceActiveInHandOffNative(getByteAddress(
                            deviceFeatures[deviceIndex].mCurrentDevice))) {
                    Log.v(TAG, "Device Active in handoff scenario");
                    return true;
                } else {
                    Log.v(TAG, "Device Not Active in handoff scenario");
                    return false;
                }
            }
        } else {
            if (!areMultipleDevicesConnected()) {
                Log.v(TAG, "Single connection exists");
                return true;
            } else {
                Log.v(TAG, "Multiple connection exists in handoff");
                if(isDeviceActiveInHandOffNative(getByteAddress(
                            deviceFeatures[deviceIndex].mCurrentDevice))) {
                    Log.v(TAG, "Device Active in handoff scenario");
                    return true;
                } else {
                    Log.v(TAG, "Device Not Active in handoff scenario");
                    return false;
                }
            }
        }
    }

    private boolean areMultipleDevicesConnected() {
        for (int deviceIndex = 0; deviceIndex < maxAvrcpConnections; deviceIndex++) {
            if (deviceFeatures[deviceIndex].mCurrentDevice == null) {
                return false;
            }
        }
        return true;
    }

    private void updatePlayerStateAndPosition(PlaybackState state) {
        if (DEBUG) Log.v(TAG, "updatePlayerPlayPauseState, old=" +
                            mCurrentPlayerState + ", state=" + state);
        if (state == null) {
            Log.i(TAG,"updatePlayerStateAndPosition: device: state = " + state);
            return;
        }

        if (DEBUG) Log.v(TAG, "old state = " + mCurrentPlayerState + ", new state= " + state);
        int oldPlayStatus = convertPlayStateToPlayStatus(mCurrentPlayerState);
        int newPlayStatus = convertPlayStateToPlayStatus(state);

        mCurrentPlayerState = state;
        mLastStateUpdate = SystemClock.elapsedRealtime();

        for (int deviceIndex = 0; deviceIndex < maxAvrcpConnections; deviceIndex++) {
            /*Discretion is required only when updating play state changed as playing*/
            if ((state.getState() != PlaybackState.STATE_PLAYING) ||
                                isPlayStateToBeUpdated(deviceIndex)) {
                updatePlayStatusForDevice(deviceIndex, state);
            }
        }

        for (int deviceIndex = 0; deviceIndex < maxAvrcpConnections; deviceIndex++) {
            sendPlayPosNotificationRsp(false, deviceIndex);
        }
    }

    private void updatePlaybackState(PlaybackState state, BluetoothDevice device) {
        Log.v(TAG,"updatePlayPauseState, state: " + state + " device: " + device);
        for (int i = 0; i < maxAvrcpConnections; i++) {
            Log.v(TAG,"Device: " + ((deviceFeatures[i].mCurrentDevice == null) ?
                "no name: " : deviceFeatures[i].mCurrentDevice.getName() +
                " : old state: " + deviceFeatures[i].mCurrentPlayState));
        }
        if (device == null) {
            /*Called because of player state change*/
            updatePlayerStateAndPosition(state);
            return;
        } else {
            int deviceIndex = getIndexForDevice(device);
            if (deviceIndex == INVALID_DEVICE_INDEX) {
                Log.w(TAG,"invalid device index" +
                        "Play status change for not connected device");
            } else {
                Log.v(TAG, "old state: " + deviceFeatures[deviceIndex].mCurrentPlayState
                            + " new state: " + state + " device: " +
                            device + " index: " + deviceIndex);
                updatePlayStatusForDevice(deviceIndex, state);
            }
        }
    }

    private void updateTransportControls(int transportControlFlags) {
        mTransportControlFlags = transportControlFlags;
    }

    class MediaAttributes {
        private boolean exists;
        private String title;
        private String artistName;
        private String albumName;
        private String mediaNumber;
        private String mediaTotalNumber;
        private String genre;
        private long playingTimeMs;
        private String coverArt;

        private static final int ATTR_TITLE = 1;
        private static final int ATTR_ARTIST_NAME = 2;
        private static final int ATTR_ALBUM_NAME = 3;
        private static final int ATTR_MEDIA_NUMBER = 4;
        private static final int ATTR_MEDIA_TOTAL_NUMBER = 5;
        private static final int ATTR_GENRE = 6;
        private static final int ATTR_PLAYING_TIME_MS = 7;
        private static final int ATTR_COVER_ART = 8;


        public MediaAttributes(MediaMetadata data) {
            exists = data != null;
            if (!exists)
                return;

            artistName = stringOrBlank(data.getString(MediaMetadata.METADATA_KEY_ARTIST));
            albumName = stringOrBlank(data.getString(MediaMetadata.METADATA_KEY_ALBUM));
            mediaNumber = longStringOrBlank(data.getLong(MediaMetadata.METADATA_KEY_TRACK_NUMBER));
            mediaTotalNumber = longStringOrBlank(data.getLong(MediaMetadata.METADATA_KEY_NUM_TRACKS));
            genre = stringOrBlank(data.getString(MediaMetadata.METADATA_KEY_GENRE));
            playingTimeMs = data.getLong(MediaMetadata.METADATA_KEY_DURATION);
            if (mAvrcpBipRsp != null)
                coverArt = stringOrBlank(mAvrcpBipRsp.getImgHandle(albumName));
            else coverArt = stringOrBlank(null);

            // Try harder for the title.
            title = data.getString(MediaMetadata.METADATA_KEY_TITLE);

            if (title == null) {
                MediaDescription desc = data.getDescription();
                if (desc != null) {
                    CharSequence val = desc.getDescription();
                    if (val != null)
                        title = val.toString();
                }
            }

            if (title == null)
                title = new String();
        }

        public long getLength() {
            if (!exists) return 0L;
            return playingTimeMs;
        }

        public boolean equals(MediaAttributes other) {
            if (other == null)
                return false;

            if (exists != other.exists)
                return false;

            if (exists == false)
                return true;

            return (title.equals(other.title)) && (artistName.equals(other.artistName))
                    && (albumName.equals(other.albumName))
                    && (mediaNumber.equals(other.mediaNumber))
                    && (mediaTotalNumber.equals(other.mediaTotalNumber))
                    && (genre.equals(other.genre)) && (playingTimeMs == other.playingTimeMs)
                    && (coverArt.equals(other.coverArt));
        }

        public String getString(int attrId) {
            if (!exists)
                return new String();

            switch (attrId) {
                case ATTR_TITLE:
                    return title;
                case ATTR_ARTIST_NAME:
                    return artistName;
                case ATTR_ALBUM_NAME:
                    return albumName;
                case ATTR_MEDIA_NUMBER:
                    return mediaNumber;
                case ATTR_MEDIA_TOTAL_NUMBER:
                    return mediaTotalNumber;
                case ATTR_GENRE:
                    return genre;
                case ATTR_PLAYING_TIME_MS:
                    return Long.toString(playingTimeMs);
                case ATTR_COVER_ART:
                    if (mAvrcpBipRsp != null) {
                        /* Fetch coverArt Handle now in case OBEX channel is established just
                        * before retrieving get element attribute. */
                        coverArt = stringOrBlank(mAvrcpBipRsp.getImgHandle(albumName));
                    } else {
                        coverArt = stringOrBlank(null);
                    }
                    return coverArt;
                default:
                    return new String();
            }
        }

        private String stringOrBlank(String s) {
            return s == null ? new String() : s;
        }

        private String longStringOrBlank(Long s) {
            return s == null ? new String() : s.toString();
        }

        public String toString() {
            if (!exists) {
                return "[MediaAttributes: none]";
            }

            return "[MediaAttributes: " + title + " - " + albumName + " by " + artistName + " ("
                    + playingTimeMs + " " + mediaNumber + "/" + mediaTotalNumber + ") " + genre
                    + " - " + coverArt + "]";
        }
    }

    private void updateCurrentMediaState(boolean registering, BluetoothDevice device) {
        MediaAttributes currentAttributes;
        PlaybackState newState = null;
        synchronized (this) {
            if (mMediaController == null) {
                boolean isPlaying = (mA2dpState == BluetoothA2dp.STATE_PLAYING) && mAudioManager.isMusicActive();
                // Use A2DP state if we don't have a MediaControlller
                PlaybackState.Builder builder = new PlaybackState.Builder();
                if (isPlaying) {
                    builder.setState(PlaybackState.STATE_PLAYING,
                            PlaybackState.PLAYBACK_POSITION_UNKNOWN, 1.0f);
                } else {
                    builder.setState(PlaybackState.STATE_PAUSED,
                            PlaybackState.PLAYBACK_POSITION_UNKNOWN, 0.0f);
                }
                newState = builder.build();
                currentAttributes = new MediaAttributes(null);
                for (int i = 0; i < maxAvrcpConnections; i++) {
                    if (device != null) {
                        if ((isPlaying != isPlayingState(deviceFeatures[i].mCurrentPlayState)) &&
                            (device.equals(deviceFeatures[i].mCurrentDevice))) {
                            if (isPlaying) {
                                deviceFeatures[i].isActiveDevice = true;
                                Log.v(TAG,"updateCurrentMediaState: Active device is set true at index = " + i);
                            }
                        }

                        if (!device.equals(deviceFeatures[i].mCurrentDevice) &&
                            deviceFeatures[i].isActiveDevice && isPlaying) {
                            deviceFeatures[i].isActiveDevice = false;
                            Log.v(TAG,"updateCurrentMediaState: Active device is set false at index = " + i);
                        }
                    }
                }
            } else {
                newState = mMediaController.getPlaybackState();
                currentAttributes = new MediaAttributes(mMediaController.getMetadata());
            }
        }

        long newQueueId = MediaSession.QueueItem.UNKNOWN_ID;
        if (newState != null) newQueueId = newState.getActiveQueueItemId();
        Log.v(TAG, "Media update: id " + mLastQueueId + "➡" + newQueueId + "? "
                        + currentAttributes.toString());
        // Notify track changed if:
        //  - The CT is registering for the notification
        //  - Queue ID is UNKNOWN and MediaMetadata is different
        //  - Queue ID is valid and different and MediaMetadata is different
        if (registering || (((newQueueId == -1) || (newQueueId != mLastQueueId))
                                   && !currentAttributes.equals(mMediaAttributes))) {
            if (registering && (device != null))
                sendTrackChangedRsp(registering, device);
            else {
                for (int i = 0; i < maxAvrcpConnections; i++) {
                    if ((deviceFeatures[i].mCurrentDevice != null) &&
                        (deviceFeatures[i].mTrackChangedNT == AvrcpConstants.NOTIFICATION_TYPE_INTERIM)) {
                        deviceFeatures[i].mTrackChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
                        deviceFeatures[i].mTracksPlayed++;
                        Log.v(TAG,"sending track change for device " + i);
                        sendTrackChangedRsp(registering, deviceFeatures[i].mCurrentDevice);
                    }
                }
            }
            mMediaAttributes = currentAttributes;
            mLastQueueId = newQueueId;
        }

        updatePlaybackState(newState, device);
    }

    private void getRcFeaturesRequestFromNative(byte[] address, int features) {
        if (DEBUG) Log.v(TAG, "getRcFeaturesRequestFromNative: address=" + address.toString());
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_GET_RC_FEATURES, features, 0,
                Utils.getAddressStringFromByte(address));
        mHandler.sendMessage(msg);
    }

    private void getPlayStatusRequestFromNative(byte[] address) {
        if (DEBUG) Log.v(TAG, "getPlayStatusRequestFromNative: address" + address.toString());
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_GET_PLAY_STATUS);
        msg.obj = address;
        mHandler.sendMessage(msg);
    }

    private void getElementAttrRequestFromNative(byte[] address, byte numAttr, int[] attrs) {
        if (DEBUG) Log.v(TAG, "getElementAttrRequestFromNative: numAttr=" + numAttr);
        AvrcpCmd avrcpCmdobj = new AvrcpCmd();
        AvrcpCmd.ElementAttrCmd elemAttr = avrcpCmdobj.new ElementAttrCmd(address, numAttr, attrs);
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_GET_ELEM_ATTRS);
        msg.obj = elemAttr;
        mHandler.sendMessage(msg);
    }

    private void registerNotificationRequestFromNative(byte[] address,int eventId, int param) {
        if (DEBUG) Log.v(TAG, "registerNotificationRequestFromNative: eventId=" + eventId);
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_REGISTER_NOTIFICATION, eventId, param);
        msg.obj = address;
        mHandler.sendMessage(msg);
    }

    private void processRegisterNotification(byte[] address, int eventId, int param) {

        BluetoothDevice device = mAdapter.getRemoteDevice(address);
        int deviceIndex = getIndexForDevice(device);
        if (deviceIndex == INVALID_DEVICE_INDEX) {
            Log.v(TAG,"device entry not present, bailing out");
            return;
        }

        int currPlayState = convertPlayStateToPlayStatus
                (deviceFeatures[deviceIndex].mCurrentPlayState);

        if (mFastforward) {
            currPlayState = PLAYSTATUS_FWD_SEEK;
        }
        if (mRewind) {
            currPlayState = PLAYSTATUS_REV_SEEK;
        }

        Log.v(TAG,"processRegisterNotification: eventId" + eventId);
        switch (eventId) {
            case EVT_PLAY_STATUS_CHANGED:
                deviceFeatures[deviceIndex].mPlayStatusChangedNT =
                        AvrcpConstants.NOTIFICATION_TYPE_INTERIM;
                registerNotificationRspPlayStatusNative(
                        deviceFeatures[deviceIndex].mPlayStatusChangedNT,
                        currPlayState,
                        getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
                break;

            case EVT_TRACK_CHANGED:
                Log.v(TAG, "Track changed notification enabled");
                mTrackChangedNT = AvrcpConstants.NOTIFICATION_TYPE_INTERIM;
                deviceFeatures[deviceIndex].mTrackChangedNT =
                        AvrcpConstants.NOTIFICATION_TYPE_INTERIM;
                updateCurrentMediaState(true, deviceFeatures[deviceIndex].mCurrentDevice);
                break;

            case EVT_PLAY_POS_CHANGED:
                if (param <= 0)
                   param = 1;

                deviceFeatures[deviceIndex].mPlayPosChangedNT =
                                             AvrcpConstants.NOTIFICATION_TYPE_INTERIM;
                deviceFeatures[deviceIndex].mPlaybackIntervalMs = (long)param * 1000L;
                sendPlayPosNotificationRsp(true, deviceIndex);
                Log.v(TAG,"mPlayPosChangedNT updated for index " +
                      deviceFeatures[deviceIndex].mPlayPosChangedNT +
                      " index " + deviceIndex);
                break;

            case EVT_AVBL_PLAYERS_CHANGED:
                /* Notify remote available players changed */
                if (DEBUG) Log.d(TAG, "Available Players notification enabled");
                deviceFeatures[deviceIndex].mAvailablePlayersChangedNT = AvrcpConstants.NOTIFICATION_TYPE_INTERIM;
                registerNotificationRspAvalPlayerChangedNative(
                        AvrcpConstants.NOTIFICATION_TYPE_INTERIM,
                        getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
                break;

            case EVT_ADDR_PLAYER_CHANGED:
                /* Notify remote addressed players changed */
                if (DEBUG) Log.d(TAG, "Addressed Player notification enabled");
                registerNotificationRspAddrPlayerChangedNative(
                        AvrcpConstants.NOTIFICATION_TYPE_INTERIM,
                        mCurrAddrPlayerID, sUIDCounter,
                        getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
                break;

            case EVENT_UIDS_CHANGED:
                if (DEBUG) Log.d(TAG, "UIDs changed notification enabled");
                registerNotificationRspUIDsChangedNative(
                        AvrcpConstants.NOTIFICATION_TYPE_INTERIM, sUIDCounter,
                        getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice));
                break;

            case EVENT_NOW_PLAYING_CONTENT_CHANGED:
                if (DEBUG) Log.d(TAG, "Now Playing List changed notification enabled");
                /* send interim response to remote device */
                if (!registerNotificationRspNowPlayingChangedNative(
                        AvrcpConstants.NOTIFICATION_TYPE_INTERIM,
                        getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice))) {
                    Log.e(TAG, "EVENT_NOW_PLAYING_CONTENT_CHANGED: " +
                            "registerNotificationRspNowPlayingChangedNative for Interim rsp failed!");
                }
                break;
        }
    }

    private void handlePassthroughCmdRequestFromNative(byte[] address, int id, int keyState) {
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_PASS_THROUGH, id, keyState);
        mHandler.sendMessage(msg);
    }

    private void sendTrackChangedRsp(boolean registering, BluetoothDevice device) {
        int deviceIndex = getIndexForDevice(device);
        if (!registering && mTrackChangedNT != AvrcpConstants.NOTIFICATION_TYPE_INTERIM) {
            if (DEBUG) Log.d(TAG, "sendTrackChangedRsp: Not registered or registering.");
            return;
        }

        mTrackChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
        if (registering) mTrackChangedNT = AvrcpConstants.NOTIFICATION_TYPE_INTERIM;
        deviceFeatures[deviceIndex].mTrackChangedNT = mTrackChangedNT;

        MediaPlayerInfo info = getAddressedPlayerInfo();
        byte[] byteAddr = getByteAddress(deviceFeatures[deviceIndex].mCurrentDevice);
        // for non-browsable players or no player
        if (info != null && !info.isBrowseSupported()) {
            byte[] track = AvrcpConstants.TRACK_IS_SELECTED;
            if (!mMediaAttributes.exists) track = AvrcpConstants.NO_TRACK_SELECTED;
            registerNotificationRspTrackChangeNative(
                              deviceFeatures[deviceIndex].mTrackChangedNT,
                              track,
                              byteAddr);
            return;
        }

        mAddressedMediaPlayer.sendTrackChangeWithId(mTrackChangedNT, mMediaController, byteAddr);
    }

    private long getPlayPosition(BluetoothDevice device) {
        if (device != null) {
            int deviceIndex = getIndexForDevice(device);
            if (deviceIndex == INVALID_DEVICE_INDEX) {
                Log.e(TAG,"Device index is not valid in getPlayPosition");
                return -1L;
            }

            if (deviceFeatures[deviceIndex].mCurrentPlayState == null)
                return -1L;

            if (deviceFeatures[deviceIndex].mCurrentPlayState.getPosition() ==
                    PlaybackState.PLAYBACK_POSITION_UNKNOWN) {
                return -1L;
            }

            if (isPlayingState(deviceFeatures[deviceIndex].mCurrentPlayState)) {
                long sinceUpdate =
                    (SystemClock.elapsedRealtime() - mLastStateUpdate +
                     deviceFeatures[deviceIndex].mCurrentPlayState.getLastPositionUpdateTime());
                return sinceUpdate + deviceFeatures[deviceIndex].mCurrentPlayState.getPosition();
            }
            return deviceFeatures[deviceIndex].mCurrentPlayState.getPosition();

        } else {
            if (mCurrentPlayerState == null)
                return -1L;

            if (mCurrentPlayerState.getPosition() == PlaybackState.PLAYBACK_POSITION_UNKNOWN)
                return -1L;

            if (isPlayingState(mCurrentPlayerState)) {
                long sinceUpdate =
                    (SystemClock.elapsedRealtime() - mCurrentPlayerState.getLastPositionUpdateTime());
                return SystemClock.elapsedRealtime() - mLastStateUpdate +
                       mCurrentPlayerState.getPosition();
            }
            return mCurrentPlayerState.getPosition();

        }
    }

    private int convertPlayStateToPlayStatus(PlaybackState state) {
        int playStatus = PLAYSTATUS_ERROR;
        switch (state.getState()) {
            case PlaybackState.STATE_PLAYING:
            case PlaybackState.STATE_BUFFERING:
                playStatus = PLAYSTATUS_PLAYING;
                break;

            case PlaybackState.STATE_STOPPED:
            case PlaybackState.STATE_NONE:
                playStatus = PLAYSTATUS_STOPPED;
                break;

            case PlaybackState.STATE_PAUSED:
                playStatus = PLAYSTATUS_PAUSED;
                break;

            case PlaybackState.STATE_FAST_FORWARDING:
            case PlaybackState.STATE_SKIPPING_TO_NEXT:
            case PlaybackState.STATE_SKIPPING_TO_QUEUE_ITEM:
                playStatus = PLAYSTATUS_FWD_SEEK;
                break;

            case PlaybackState.STATE_REWINDING:
            case PlaybackState.STATE_SKIPPING_TO_PREVIOUS:
                playStatus = PLAYSTATUS_REV_SEEK;
                break;

            case PlaybackState.STATE_ERROR:
                playStatus = PLAYSTATUS_ERROR;
                break;

        }
        return playStatus;
    }

    private boolean isPlayingState(PlaybackState state) {
        return (state.getState() == PlaybackState.STATE_PLAYING) ||
                (state.getState() == PlaybackState.STATE_BUFFERING);
    }

    /**
     * Sends a play position notification, or schedules one to be
     * sent later at an appropriate time. If |requested| is true,
     * does both because this was called in reponse to a request from the
     * TG.
     */
    private void sendPlayPosNotificationRsp(boolean requested, int i) {
        if (!requested && deviceFeatures[i].mPlayPosChangedNT != AvrcpConstants.NOTIFICATION_TYPE_INTERIM) {
            if (DEBUG) Log.d(TAG, "sendPlayPosNotificationRsp: Not registered or requesting.");
            return;
        }
        long playPositionMs = getPlayPosition(deviceFeatures[i].mCurrentDevice);
        int currPlayStatus = convertPlayStateToPlayStatus(deviceFeatures[i].mCurrentPlayState);
        String debugLine = "sendPlayPosNotificationRsp: ";

        // Some remote devices are going to bad state when sending play position
        // as ffff for non-playing state
        if (!requested && playPositionMs == -1L && currPlayStatus != PLAYSTATUS_PLAYING) {
           if (DEBUG) Log.d(TAG, " Don't send invalid play position notification for non-playing state");
           return;
        }

        // mNextPosMs is set to -1 when the previous position was invalid
        // so this will be true if the new position is valid & old was invalid.
        // mPlayPositionMs is set to -1 when the new position is invalid,
        // and the old mPrevPosMs is >= 0 so this is true when the new is invalid
        // and the old was valid.
        if (DEBUG) {
            debugLine += "(" + requested + ") " + deviceFeatures[i].mPrevPosMs + " <=? " + playPositionMs + " <=? "
                    + deviceFeatures[i].mNextPosMs;
            if (isPlayingState(deviceFeatures[i].mCurrentPlayState)) debugLine += " Playing";
            debugLine += " State: " + deviceFeatures[i].mCurrentPlayState.getState();
        }
        if (requested || ((deviceFeatures[i].mLastReportedPosition != playPositionMs) &&
             (playPositionMs >= deviceFeatures[i].mNextPosMs) ||
             (playPositionMs <= deviceFeatures[i].mPrevPosMs))) {
            if (!requested) deviceFeatures[i].mPlayPosChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
            registerNotificationRspPlayPosNative(deviceFeatures[i].mPlayPosChangedNT,
                   (int)playPositionMs, getByteAddress(deviceFeatures[i].mCurrentDevice));
            deviceFeatures[i].mLastReportedPosition = playPositionMs;
            if (playPositionMs != PlaybackState.PLAYBACK_POSITION_UNKNOWN) {
                deviceFeatures[i].mNextPosMs = playPositionMs + deviceFeatures[i].mPlaybackIntervalMs;
                deviceFeatures[i].mPrevPosMs = playPositionMs - deviceFeatures[i].mPlaybackIntervalMs;
            } else {
                deviceFeatures[i].mNextPosMs = -1;
                deviceFeatures[i].mPrevPosMs = -1;
            }
        }

        mHandler.removeMessages(MSG_PLAY_INTERVAL_TIMEOUT);
        if (deviceFeatures[i].mPlayPosChangedNT == AvrcpConstants.NOTIFICATION_TYPE_INTERIM &&
                 isPlayingState(deviceFeatures[i].mCurrentPlayState)) {
            Message msg = mHandler.obtainMessage(MSG_PLAY_INTERVAL_TIMEOUT, 0, 0,
                                                 deviceFeatures[i].mCurrentDevice);
            long delay = deviceFeatures[i].mPlaybackIntervalMs;
            if (deviceFeatures[i].mNextPosMs != -1) {
                delay = deviceFeatures[i].mNextPosMs - (playPositionMs > 0 ? playPositionMs : 0);
            }
            if (DEBUG) debugLine += " Timeout " + delay + "ms";
            mHandler.sendMessageDelayed(msg, delay);
        }
        if (DEBUG) Log.d(TAG, debugLine);
    }

    /**
     * This is called from AudioService. It will return whether this device supports abs volume.
     * NOT USED AT THE MOMENT.
     */
    public boolean isAbsoluteVolumeSupported() {
        if (mA2dpService.isMulticastFeatureEnabled() &&
                areMultipleDevicesConnected()) {
            if (DEBUG) Log.v(TAG, "isAbsoluteVolumeSupported : Absolute volume false multicast is enabled & multiple devices are connected");
            return false;
        }
        List<Byte> absVolumeSupported = new ArrayList<Byte>();
        for (int i = 0; i < maxAvrcpConnections; i++) {
            if (deviceFeatures[i].mCurrentDevice != null) {
                // add 1 in byte list if absolute volume is supported
                // add 0 in byte list if absolute volume not supported
                if ((deviceFeatures[i].mFeatures &
                        BTRC_FEAT_ABSOLUTE_VOLUME) != 0) {
                    Log.v(TAG, "isAbsoluteVolumeSupported: yes, for dev: " + i);
                    absVolumeSupported.add((byte)1);
                } else {
                    Log.v(TAG, "isAbsoluteVolumeSupported: no, for dev: " + i);
                    absVolumeSupported.add((byte)0);
                }
            }
        }
        return !(absVolumeSupported.contains((byte)0) || absVolumeSupported.isEmpty());
    }

    /**
     * We get this call from AudioService. This will send a message to our handler object,
     * requesting our handler to call setVolumeNative()
     */
    public void adjustVolume(int direction) {
        Log.d(TAG, "pts_test = " + pts_test + " direction = " + direction);
        if (pts_test) {
/* TODOuv
            AvrcpControllerService avrcpCtrlService =
                    AvrcpControllerService.getAvrcpControllerService();
            if (avrcpCtrlService != null) {
                Log.d(TAG, "avrcpCtrlService not null");
                for (int i = 0; i < maxAvrcpConnections; i++) {
                    if (deviceFeatures[i].mCurrentDevice != null) {
                        Log.d(TAG, "SendPassThruPlay command sent for = "
                                + deviceFeatures[i].mCurrentDevice);
                        if (direction == 1) {
                            avrcpCtrlService.sendPassThroughCmd(
                                deviceFeatures[i].mCurrentDevice, AVRC_ID_VOL_UP,
                                AvrcpConstants.KEY_STATE_PRESS);
                            avrcpCtrlService.sendPassThroughCmd(
                                deviceFeatures[i].mCurrentDevice, AVRC_ID_VOL_UP,
                                AvrcpConstants.KEY_STATE_RELEASE);
                        } else if (direction == -1) {
                           avrcpCtrlService.sendPassThroughCmd(
                                deviceFeatures[i].mCurrentDevice, AVRC_ID_VOL_DOWN,
                                AvrcpConstants.KEY_STATE_PRESS);
                           avrcpCtrlService.sendPassThroughCmd(
                                deviceFeatures[i].mCurrentDevice, AVRC_ID_VOL_DOWN,
                                AvrcpConstants.KEY_STATE_RELEASE);
                        }
                    }
                }
            } else {
                Log.d(TAG, "passthru command not sent, connection unavailable");
            }
*/
        } else {
            Log.d(TAG, "MSG_ADJUST_VOLUME");
            Message msg = mHandler.obtainMessage(MSG_ADJUST_VOLUME, direction, 0);
            mHandler.sendMessage(msg);
        }
    }

    public void setAbsoluteVolume(int volume) {
        if (volume == mLocalVolume) {
            if (DEBUG) Log.v(TAG, "setAbsoluteVolume is setting same index, ignore "+volume);
            return;
        }

        mHandler.removeMessages(MSG_ADJUST_VOLUME);
        Message msg = mHandler.obtainMessage(MSG_SET_ABSOLUTE_VOLUME, volume, 0);
        mHandler.sendMessage(msg);
    }

    /* Called in the native layer as a btrc_callback to return the volume set on the carkit in the
     * case when the volume is change locally on the carkit. This notification is not called when
     * the volume is changed from the phone.
     *
     * This method will send a message to our handler to change the local stored volume and notify
     * AudioService to update the UI
     */
    private void volumeChangeRequestFromNative(byte[] address, int volume, int ctype) {
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_VOLUME_CHANGE, volume, ctype);
        Bundle data = new Bundle();
        data.putByteArray("BdAddress" , address);
        msg.setData(data);
        mHandler.sendMessage(msg);
    }

    private void getFolderItemsRequestFromNative(
        byte[] address, byte scope, long startItem, long endItem, byte numAttr, int[] attrIds) {
        if (DEBUG) Log.v(TAG, "getFolderItemsRequestFromNative: scope=" + scope + ", numAttr=" + numAttr);
        AvrcpCmd avrcpCmdobj = new AvrcpCmd();
        AvrcpCmd.FolderItemsCmd folderObj = avrcpCmdobj.new FolderItemsCmd(address, scope,
                startItem, endItem, numAttr, attrIds);
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_GET_FOLDER_ITEMS, 0, 0);
        msg.obj = folderObj;
        mHandler.sendMessage(msg);
    }

    private void setAddressedPlayerRequestFromNative(byte[] address, int playerId) {
        if (DEBUG) Log.v(TAG, "setAddrPlayerRequestFromNative: playerId=" + playerId);
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_SET_ADDR_PLAYER, playerId, 0);
        msg.obj = address;
        mHandler.sendMessage(msg);
    }

    private void setBrowsedPlayerRequestFromNative(byte[] address, int playerId) {
        if (DEBUG) Log.v(TAG, "setBrPlayerRequestFromNative: playerId=" + playerId);
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_SET_BR_PLAYER, playerId, 0);
        msg.obj = address;
        mHandler.sendMessage(msg);
    }

    private void changePathRequestFromNative(byte[] address, byte direction, byte[] folderUid) {
        if (DEBUG) Log.v(TAG, "changePathRequestFromNative: direction=" + direction);
        Bundle data = new Bundle();
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_CHANGE_PATH);
        data.putByteArray("BdAddress" , address);
        data.putByteArray("folderUid" , folderUid);
        data.putByte("direction" , direction);
        msg.setData(data);
        mHandler.sendMessage(msg);
    }

    private void getItemAttrRequestFromNative(byte[] address, byte scope, byte[] itemUid, int uidCounter,
            byte numAttr, int[] attrs) {
        AvrcpCmd avrcpCmdobj = new AvrcpCmd();
        AvrcpCmd.ItemAttrCmd itemAttr = avrcpCmdobj.new ItemAttrCmd(address, scope,
                itemUid, uidCounter, numAttr, attrs);
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_GET_ITEM_ATTR);
        msg.obj = itemAttr;
        mHandler.sendMessage(msg);
    }

    private void searchRequestFromNative(byte[] address, int charsetId, byte[] searchStr) {
        /* Search is not supported */
        Log.w(TAG, "searchRequestFromNative: search is not supported");
        searchRspNative(address, AvrcpConstants.RSP_SRCH_NOT_SPRTD, 0, 0);
    }

    private void playItemRequestFromNative(byte[] address, byte scope, int uidCounter, byte[] uid) {
        if (DEBUG) Log.v(TAG, "playItemRequestFromNative: scope=" + scope);
        Bundle data = new Bundle();
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_PLAY_ITEM);
        data.putByteArray("BdAddress" , address);
        data.putByteArray("uid" , uid);
        data.putInt("uidCounter" , uidCounter);
        data.putByte("scope" , scope);
        msg.setData(data);
        mHandler.sendMessage(msg);
    }

    private void addToPlayListRequestFromNative(byte[] address, byte scope, byte[] uid, int uidCounter) {
        /* add to NowPlaying not supported */
        Log.w(TAG, "addToPlayListRequestFromNative: not supported! scope=" + scope);
        addToNowPlayingRspNative(address, AvrcpConstants.RSP_INTERNAL_ERR);
    }

    private void getTotalNumOfItemsRequestFromNative(byte[] address, byte scope) {
        if (DEBUG) Log.v(TAG, "getTotalNumOfItemsRequestFromNative: scope=" + scope);
        Bundle data = new Bundle();
        Message msg = mHandler.obtainMessage(MSG_NATIVE_REQ_GET_TOTAL_NUM_OF_ITEMS);
        msg.arg1 = scope;
        msg.obj = address;
        mHandler.sendMessage(msg);
    }

    private void notifyVolumeChanged(int volume) {
        mAudioManager.setStreamVolume(AudioManager.STREAM_MUSIC, volume,
                      AudioManager.FLAG_SHOW_UI | AudioManager.FLAG_BLUETOOTH_ABS_VOLUME);
    }

    private int convertToAudioStreamVolume(int volume) {
        // Rescale volume to match AudioSystem's volume
        return (int) Math.floor((double) volume*mAudioStreamMax/AVRCP_MAX_VOL);
    }

    private int convertToAvrcpVolume(int volume) {
        return (int) Math.ceil((double) volume*AVRCP_MAX_VOL/mAudioStreamMax);
    }

    private void blackListCurrentDevice(int i) {
        String mAddress = null;
        if (deviceFeatures[i].mCurrentDevice == null) {
            Log.v(TAG, "blackListCurrentDevice: Device is null");
            return;
        }
        mAddress  = deviceFeatures[i].mCurrentDevice.getAddress();
        deviceFeatures[i].mFeatures &= ~BTRC_FEAT_ABSOLUTE_VOLUME;
        mAudioManager.avrcpSupportsAbsoluteVolume(mAddress, isAbsoluteVolumeSupported());

        SharedPreferences pref = mContext.getSharedPreferences(ABSOLUTE_VOLUME_BLACKLIST,
                Context.MODE_PRIVATE);
        SharedPreferences.Editor editor = pref.edit();
        editor.putBoolean(mAddress, true);
        editor.commit();
    }


    private int modifyRcFeatureFromBlacklist(int feature, String address) {
        SharedPreferences pref = mContext.getSharedPreferences(ABSOLUTE_VOLUME_BLACKLIST,
                Context.MODE_PRIVATE);
        if (!pref.contains(address)) {
            return feature;
        }
        if (pref.getBoolean(address, false)) {
            feature &= ~BTRC_FEAT_ABSOLUTE_VOLUME;
        }
        return feature;
    }

    public void resetBlackList(String address) {
        SharedPreferences pref = mContext.getSharedPreferences(ABSOLUTE_VOLUME_BLACKLIST,
                Context.MODE_PRIVATE);
        SharedPreferences.Editor editor = pref.edit();
        editor.remove(address);
        editor.apply();
    }

    /**
     * This is called from A2dpStateMachine to set A2dp audio state.
     */
    public void setA2dpAudioState(int state, BluetoothDevice device) {
        Message msg = mHandler.obtainMessage(MSG_SET_A2DP_AUDIO_STATE, state, 0, device);
        mHandler.sendMessage(msg);
    }

    public void setAvrcpConnectedDevice(BluetoothDevice device) {
        Log.i(TAG,"Device added is " + device);
        for (int i = 0; i < maxAvrcpConnections; i++) {
            if (deviceFeatures[i].mCurrentDevice != null &&
                    deviceFeatures[i].mCurrentDevice.equals(device)) {
                Log.v(TAG,"device is already added in connected list, ignore now");
                return;
            }
        }
        for (int i = 0; i < maxAvrcpConnections; i++ ) {
            if (deviceFeatures[i].mCurrentDevice == null) {
                deviceFeatures[i].mCurrentDevice = device;
                deviceFeatures[i].isActiveDevice = true;
                /*Playstate is explicitly updated here to take care of cases
                        where play state update is missed because of that happening
                        even before Avrcp connects*/
                deviceFeatures[i].mCurrentPlayState = mCurrentPlayerState;
                if (isPlayingState(mCurrentPlayerState)) {
                /* In dual a2dp connection mode, if music is streaming on other device and
                ** avrcp connection was delayed to second device and is not in playing state
                ** check for playing device and update play status accordingly
                */
                    if (!isPlayStateToBeUpdated(i)) {
                        PlaybackState.Builder playState = new PlaybackState.Builder();
                        playState.setState(PlaybackState.STATE_PAUSED,
                                       PlaybackState.PLAYBACK_POSITION_UNKNOWN, 1.0f);
                        deviceFeatures[i].mCurrentPlayState = playState.build();
                    }
                }
                if (!isPlayingState(mCurrentPlayerState) &&
                     mA2dpService.getA2dpPlayingDevice().size() > 0) {
                /*A2DP playstate updated for video playback scenario, where a2dp play status is
                    updated when avrcp connection was not up yet.*/
                    Log.i(TAG,"A2dp playing device found");
                    List<BluetoothDevice> playingDevice = mA2dpService.getA2dpPlayingDevice();
                    for (int j = 0; j < playingDevice.size(); j++) {
                        if (playingDevice.get(j).equals(device)) {
                            PlaybackState.Builder playState = new PlaybackState.Builder();
                            playState.setState(PlaybackState.STATE_PLAYING,
                                           PlaybackState.PLAYBACK_POSITION_UNKNOWN, 1.0f);
                            deviceFeatures[i].mCurrentPlayState = playState.build();
                        }
                    }
                }
                Log.i(TAG,"play status updated on Avrcp connection as: " +
                                                    deviceFeatures[i].mCurrentPlayState);
                Log.i(TAG,"device added at " + i);
                Log.i(TAG,"Active device set to true at index =  " + i);
                break;
            }
        }

        for (int i = 0; i < maxAvrcpConnections; i++ ) {
            if (isPlayingState(mCurrentPlayerState)) {
                if (deviceFeatures[i].mCurrentDevice != null &&
                    !isPlayStateToBeUpdated(i) &&
                    deviceFeatures[i].isActiveDevice) {
                    deviceFeatures[i].isActiveDevice = false;
                    Log.i(TAG,"Active device set to false at index =  " + i);
                }
            }
            else if (deviceFeatures[i].mCurrentDevice != null &&
                    !(deviceFeatures[i].mCurrentDevice.equals(device)) &&
                    deviceFeatures[i].isActiveDevice) {
                deviceFeatures[i].isActiveDevice = false;
                Log.i(TAG,"Active device set to false at index =  " + i);
            }
        }
    }

    /**
     * This is called from A2dpStateMachine to set A2dp Connected device to null on disconnect.
     */
    public void setAvrcpDisconnectedDevice(BluetoothDevice device) {
        for (int i = 0; i < maxAvrcpConnections; i++ ) {
            if (deviceFeatures[i].mCurrentDevice !=null &&
                    deviceFeatures[i].mCurrentDevice.equals(device)) {
                // initiate cleanup for all variables;
                Message msg = mHandler.obtainMessage(MESSAGE_DEVICE_RC_CLEANUP, STACK_CLEANUP,
                       0, device);
                mHandler.sendMessage(msg);
                Log.i(TAG,"Device removed is " + device);
                Log.i(TAG,"removed at " + i);
                /* device is disconnect and some response form music app was
                 * pending for this device clear it.*/
// TODOuv
//                if (mBrowserDevice != null &&
//                        mBrowserDevice.equals(device)) {
//                    Log.i(TAG,"clearing mBrowserDevice on disconnect");
//                    mBrowserDevice = null;
//                }
            }
            /* Multicast scenario both abs vol supported
               Active device got disconnected so make other
               device which is left supporting absolute
               volume as active device
            */
            if (deviceFeatures[i].mCurrentDevice != null &&
                    !(deviceFeatures[i].mCurrentDevice.equals(device))) {
                deviceFeatures[i].isActiveDevice = true;
                Log.i(TAG,"setAvrcpDisconnectedDevice : Active device changed to index = " + i);
            }
        }
        mAudioManager.avrcpSupportsAbsoluteVolume(device.getAddress(),
                isAbsoluteVolumeSupported());
        Log.v(TAG," update audio manager for abs vol state = "
                + isAbsoluteVolumeSupported());
        for (int i = 0; i < maxAvrcpConnections; i++ ) {
            if (deviceFeatures[i].mCurrentDevice != null) {
                if (isAbsoluteVolumeSupported() &&
                        deviceFeatures[i].mAbsoluteVolume != -1) {
                    notifyVolumeChanged(deviceFeatures[i].mAbsoluteVolume);
                    Log.v(TAG," update audio manager for abs vol  = "
                            + deviceFeatures[i].mAbsoluteVolume);
                }
                break;
            }
        }
    }

    private class AvrcpServiceBootReceiver extends BroadcastReceiver {
        @Override
        public void onReceive(Context context, Intent intent) {
            String action = intent.getAction();
            if (action.equals(Intent.ACTION_BOOT_COMPLETED)) {
                if (DEBUG) Log.d(TAG, "Boot completed, initializing player lists");
                /* initializing media player's list */
                mBrowsableListBuilder.start();
            }
        }
    }

    private class AvrcpServiceBroadcastReceiver extends BroadcastReceiver {
        @Override
        public void onReceive(Context context, Intent intent) {
            String action = intent.getAction();
            if (DEBUG) Log.d(TAG, "AvrcpServiceBroadcastReceiver-> Action: " + action);

            if (action.equals(Intent.ACTION_PACKAGE_REMOVED)
                    || action.equals(Intent.ACTION_PACKAGE_DATA_CLEARED)) {
                if (!intent.getBooleanExtra(Intent.EXTRA_REPLACING, false)) {
                    // a package is being removed, not replaced
                    String packageName = intent.getData().getSchemeSpecificPart();
                    if (packageName != null) {
                        handlePackageModified(packageName, true);
                    }
                }

            } else if (action.equals(Intent.ACTION_PACKAGE_ADDED)
                    || action.equals(Intent.ACTION_PACKAGE_CHANGED)) {
                String packageName = intent.getData().getSchemeSpecificPart();
                if (DEBUG) Log.d(TAG,"AvrcpServiceBroadcastReceiver-> packageName: "
                        + packageName);
                if (packageName != null) {
                    handlePackageModified(packageName, false);
                }
            }
        }
    }

    private void handlePackageModified(String packageName, boolean removed) {
        if (DEBUG) Log.d(TAG, "packageName: " + packageName + " removed: " + removed);

        if (removed) {
            removeMediaPlayerInfo(packageName);
            // old package is removed, updating local browsable player's list
            if (isBrowseSupported(packageName)) {
                removePackageFromBrowseList(packageName);
            }
        } else {
            // new package has been added.
            if (isBrowsableListUpdated(packageName)) {
                // Rebuilding browsable players list
                mBrowsableListBuilder.start();
            }
        }
    }

    private boolean isBrowsableListUpdated(String newPackageName) {
        // getting the browsable media players list from package manager
        Intent intent = new Intent("android.media.browse.MediaBrowserService");
        List<ResolveInfo> resInfos = mPackageManager.queryIntentServices(intent,
                                         PackageManager.MATCH_ALL);
        for (ResolveInfo resolveInfo : resInfos) {
            if (resolveInfo.serviceInfo.packageName.equals(newPackageName)) {
                if (DEBUG)
                    Log.d(TAG,
                            "isBrowsableListUpdated: package includes MediaBrowserService, true");
                return true;
            }
        }

        // if list has different size
        if (resInfos.size() != mBrowsePlayerInfoList.size()) {
            if (DEBUG) Log.d(TAG, "isBrowsableListUpdated: browsable list size mismatch, true");
            return true;
        }

        Log.d(TAG, "isBrowsableListUpdated: false");
        return false;
    }

    private void removePackageFromBrowseList(String packageName) {
        if (DEBUG) Log.d(TAG, "removePackageFromBrowseList: " + packageName);
        synchronized (mBrowsePlayerInfoList) {
            int browseInfoID = getBrowseId(packageName);
            if (browseInfoID != -1) {
                mBrowsePlayerInfoList.remove(browseInfoID);
            }
        }
    }

    /*
     * utility function to get the browse player index from global browsable
     * list. It may return -1 if specified package name is not in the list.
     */
    private int getBrowseId(String packageName) {
        boolean response = false;
        int browseInfoID = 0;
        synchronized (mBrowsePlayerInfoList) {
            for (BrowsePlayerInfo info : mBrowsePlayerInfoList) {
                if (info.packageName.equals(packageName)) {
                    response = true;
                    break;
                }
                browseInfoID++;
            }
        }

        if (!response) {
            browseInfoID = -1;
        }

        if (DEBUG) Log.d(TAG, "getBrowseId for packageName: " + packageName +
                " , browseInfoID: " + browseInfoID);
        return browseInfoID;
    }

    private void setAddressedPlayer(byte[] bdaddr, int selectedId) {
        String functionTag = "setAddressedPlayer(" + selectedId + "): ";

        synchronized (mMediaPlayerInfoList) {
            if (mMediaPlayerInfoList.isEmpty()) {
                Log.w(TAG, functionTag + "no players, send no available players");
                setAddressedPlayerRspNative(bdaddr, AvrcpConstants.RSP_NO_AVBL_PLAY);
                return;
            }
            if (!mMediaPlayerInfoList.containsKey(selectedId)) {
                Log.w(TAG, functionTag + "invalid id, sending response back ");
                setAddressedPlayerRspNative(bdaddr, AvrcpConstants.RSP_INV_PLAYER);
                return;
            }

            if (isPlayerAlreadyAddressed(selectedId)) {
                MediaPlayerInfo info = getAddressedPlayerInfo();
                Log.i(TAG, functionTag + "player already addressed: " + info);
                setAddressedPlayerRspNative(bdaddr, AvrcpConstants.RSP_NO_ERROR);
                return;
            }
            // register new Media Controller Callback and update the current IDs
            if (!updateCurrentController(selectedId, mCurrBrowsePlayerID)) {
                Log.e(TAG, functionTag + "updateCurrentController failed!");
                setAddressedPlayerRspNative(bdaddr, AvrcpConstants.RSP_INTERNAL_ERR);
                return;
            }
            // If we don't have a controller, try to launch the player
            MediaPlayerInfo info = getAddressedPlayerInfo();
            if (info.getMediaController() == null) {
                Intent launch = mPackageManager.getLaunchIntentForPackage(info.getPackageName());
                Log.i(TAG, functionTag + "launching player " + launch);
                mContext.startActivity(launch);
            }
        }
        setAddressedPlayerRspNative(bdaddr, AvrcpConstants.RSP_NO_ERROR);
    }

    private void setBrowsedPlayer(byte[] bdaddr, int selectedId) {
        int status = AvrcpConstants.RSP_NO_ERROR;

        // checking for error cases
        if (mMediaPlayerInfoList.isEmpty()) {
            status = AvrcpConstants.RSP_NO_AVBL_PLAY;
            Log.w(TAG, " No Available Players to set, sending response back ");
        } else {
            // update current browse player id and start browsing service
            updateNewIds(mCurrAddrPlayerID, selectedId);
            String browsedPackage = getPackageName(selectedId);

            if (!isPackageNameValid(browsedPackage)) {
                Log.w(TAG, " Invalid package for id:" + mCurrBrowsePlayerID);
                status = AvrcpConstants.RSP_INV_PLAYER;
            } else if (!isBrowseSupported(browsedPackage)) {
                Log.w(TAG, "Browse unsupported for id:" + mCurrBrowsePlayerID
                        + ", packagename : " + browsedPackage);
                status = AvrcpConstants.RSP_PLAY_NOT_BROW;
            } else if (!startBrowseService(bdaddr, browsedPackage)) {
                Log.e(TAG, "service cannot be started for browse player id:" + mCurrBrowsePlayerID
                        + ", packagename : " + browsedPackage);
                status = AvrcpConstants.RSP_INTERNAL_ERR;
            }
        }

        if (status != AvrcpConstants.RSP_NO_ERROR) {
            setBrowsedPlayerRspNative(bdaddr, status, (byte) 0x00, 0, null);
        }

        if (DEBUG) Log.d(TAG, "setBrowsedPlayer for selectedId: " + selectedId +
                " , status: " + status);
    }

    private MediaSessionManager.OnActiveSessionsChangedListener mActiveSessionListener =
            new MediaSessionManager.OnActiveSessionsChangedListener() {

                @Override
                public void onActiveSessionsChanged(
                        List<android.media.session.MediaController> newControllers) {
                    boolean playersChanged = false;

                    // Update the current players
                    for (android.media.session.MediaController controller : newControllers) {
                        addMediaPlayerController(controller);
                        playersChanged = true;
                    }

                    if (playersChanged) {
                        mHandler.sendEmptyMessage(MSG_AVAILABLE_PLAYERS_CHANGED_RSP);
                        if (newControllers.size() > 0 && getAddressedPlayerInfo() == null) {
                            if (DEBUG)
                                Log.v(TAG,
                                        "No addressed player but active sessions, taking first.");
                            setAddressedMediaSessionPackage(newControllers.get(0).getPackageName());
                        }
                    }
                }
            };

    private void setAddressedMediaSessionPackage(@Nullable String packageName) {
        if (packageName == null) {
            // Should only happen when there's no media players, reset to no available player.
            updateCurrentController(0, mCurrBrowsePlayerID);
            return;
        }
        // No change.
        if (getPackageName(mCurrAddrPlayerID).equals(packageName)) return;
        if (DEBUG) Log.v(TAG, "Changing addressed media session to " + packageName);
        // If the player doesn't exist, we need to add it.
        if (getMediaPlayerInfo(packageName) == null) {
            addMediaPlayerPackage(packageName);
            mHandler.sendEmptyMessage(MSG_AVAILABLE_PLAYERS_CHANGED_RSP);
        }
        synchronized (mMediaPlayerInfoList) {
            for (Map.Entry<Integer, MediaPlayerInfo> entry : mMediaPlayerInfoList.entrySet()) {
                if (entry.getValue().getPackageName().equals(packageName)) {
                    int newAddrID = entry.getKey();
                    if (DEBUG) Log.v(TAG, "Set addressed #" + newAddrID + " " + entry.getValue());
                    updateCurrentController(newAddrID, mCurrBrowsePlayerID);
                    mHandler.obtainMessage(MSG_ADDRESSED_PLAYER_CHANGED_RSP, newAddrID, 0)
                            .sendToTarget();
                    return;
                }
            }
        }
        // We shouldn't ever get here.
        Log.e(TAG, "Player info for " + packageName + " doesn't exist!");
    }

    private void setActiveMediaSession(MediaSession.Token token) {
        android.media.session.MediaController activeController =
                new android.media.session.MediaController(mContext, token);
        if (DEBUG) Log.v(TAG, "Set active media session " + activeController.getPackageName());
        addMediaPlayerController(activeController);
        setAddressedMediaSessionPackage(activeController.getPackageName());
    }

    private boolean startBrowseService(byte[] bdaddr, String packageName) {
        boolean status = true;

        /* creating new instance for Browse Media Player */
        String browseService = getBrowseServiceName(packageName);
        if (!browseService.isEmpty()) {
            mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr).setBrowsed(
                    packageName, browseService);
        } else {
            Log.w(TAG, "No Browser service available for " + packageName);
            status = false;
        }

        if (DEBUG) Log.d(TAG, "startBrowseService for packageName: " + packageName +
                ", status = " + status);
        return status;
    }

    private String getBrowseServiceName(String packageName) {
        String browseServiceName = "";

        // getting the browse service name from browse player info
        synchronized (mBrowsePlayerInfoList) {
            int browseInfoID = getBrowseId(packageName);
            if (browseInfoID != -1) {
                browseServiceName = mBrowsePlayerInfoList.get(browseInfoID).serviceClass;
            }
        }

        if (DEBUG) Log.d(TAG, "getBrowseServiceName for packageName: " + packageName +
                ", browseServiceName = " + browseServiceName);
        return browseServiceName;
    }

    private class BrowsablePlayerListBuilder extends MediaBrowser.ConnectionCallback {
        List<ResolveInfo> mWaiting;
        BrowsePlayerInfo mCurrentPlayer;
        MediaBrowser mCurrentBrowser;
        boolean mPlayersChanged;

        public BrowsablePlayerListBuilder() {}

        public void start() {
            mBrowsePlayerInfoList.clear();
            cleanup();
            Intent intent = new Intent(android.service.media.MediaBrowserService.SERVICE_INTERFACE);
            mWaiting = mPackageManager.queryIntentServices(intent, PackageManager.MATCH_ALL);
            connectNextPlayer();
        }

        public void cleanup() {
            if (mWaiting != null) mWaiting.clear();
            mPlayersChanged = false;
            if (mCurrentBrowser != null) mCurrentBrowser.disconnect();
        }

        private void connectNextPlayer() {
            if (mWaiting.isEmpty()) {
                // Done. Send players changed if needed.
                if (mPlayersChanged) {
                   for (int i = 0; i < maxAvrcpConnections; i++) {
                       if (deviceFeatures[i].mAvailablePlayersChangedNT ==
                               AvrcpConstants.NOTIFICATION_TYPE_INTERIM) {
                           deviceFeatures[i].mAvailablePlayersChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
                           if (DEBUG)
                               Log.v(TAG, "send AvailableMediaPlayers to stack");
                           registerNotificationRspAvalPlayerChangedNative(
                                   deviceFeatures[i].mAvailablePlayersChangedNT,
                                   getByteAddress(deviceFeatures[i].mCurrentDevice));
                       }
                   }
                }
                return;
            }
            ResolveInfo info = mWaiting.remove(0);
            String displayableName = info.loadLabel(mPackageManager).toString();
            String serviceName = info.serviceInfo.name;
            String packageName = info.serviceInfo.packageName;

            mCurrentPlayer = new BrowsePlayerInfo(packageName, displayableName, serviceName);
            mCurrentBrowser = new MediaBrowser(
                    mContext, new ComponentName(packageName, serviceName), this, null);
            if (DEBUG) Log.d(TAG, "Trying to connect to " + serviceName);
            mCurrentBrowser.connect();
        }

        @Override
        public void onConnected() {
            Log.d(TAG, "BrowsablePlayerListBuilder: " + mCurrentPlayer.packageName + " OK");
            mCurrentBrowser.disconnect();
            mCurrentBrowser = null;
            mBrowsePlayerInfoList.add(mCurrentPlayer);
            MediaPlayerInfo info = getMediaPlayerInfo(mCurrentPlayer.packageName);
            MediaController controller = (info == null) ? null : info.getMediaController();
            // Refresh the media player entry so it notices we can browse
            if (controller != null) {
                addMediaPlayerController(controller.getWrappedInstance());
            } else {
                addMediaPlayerPackage(mCurrentPlayer.packageName);
            }
            mPlayersChanged = true;
            connectNextPlayer();
        }

        @Override
        public void onConnectionFailed() {
            Log.d(TAG, "BrowsablePlayerListBuilder: " + mCurrentPlayer.packageName + " FAIL");
            connectNextPlayer();
        }
    }

    /* Initializes list of media players identified from session manager active sessions */
    private void initMediaPlayersList() {
        synchronized (mMediaPlayerInfoList) {
            // Clearing old browsable player's list
            mMediaPlayerInfoList.clear();

            if (mMediaSessionManager == null) {
                if (DEBUG) Log.w(TAG, "initMediaPlayersList: no media session manager!");
                return;
            }

            List<android.media.session.MediaController> controllers =
                    mMediaSessionManager.getActiveSessions(null);
            if (DEBUG)
                Log.v(TAG, "initMediaPlayerInfoList: " + controllers.size() + " controllers");
            /* Initializing all media players */
            for (android.media.session.MediaController controller : controllers) {
                addMediaPlayerController(controller);
            }
            if (controllers.size() > 0) {
                mHandler.sendEmptyMessage(MSG_AVAILABLE_PLAYERS_CHANGED_RSP);
            }

            if (mMediaPlayerInfoList.size() > 0) {
                // Set the first one as the Addressed Player
                updateCurrentController(mMediaPlayerInfoList.firstKey(), -1);
            }
        }
    }

    private List<android.media.session.MediaController> getMediaControllers() {
        List<android.media.session.MediaController> controllers =
                new ArrayList<android.media.session.MediaController>();
        synchronized (mMediaPlayerInfoList) {
            for (MediaPlayerInfo info : mMediaPlayerInfoList.values()) {
                MediaController controller = info.getMediaController();
                if (controller != null) {
                    controllers.add(controller.getWrappedInstance());
                }
            }
        }
        return controllers;
    }

    /** Add (or update) a player to the media player list without a controller */
    private boolean addMediaPlayerPackage(String packageName) {
        MediaPlayerInfo info = new MediaPlayerInfo(null, AvrcpConstants.PLAYER_TYPE_AUDIO,
                AvrcpConstants.PLAYER_SUBTYPE_NONE, getPlayStateBytes(null),
                getFeatureBitMask(packageName), packageName, getAppLabel(packageName));
        return addMediaPlayerInfo(info);
    }

    /** Add (or update) a player to the media player list given an active controller */
    private boolean addMediaPlayerController(android.media.session.MediaController controller) {
        String packageName = controller.getPackageName();
        MediaPlayerInfo info = new MediaPlayerInfo(MediaController.wrap(controller),
                AvrcpConstants.PLAYER_TYPE_AUDIO, AvrcpConstants.PLAYER_SUBTYPE_NONE,
                getPlayStateBytes(controller.getPlaybackState()), getFeatureBitMask(packageName),
                controller.getPackageName(), getAppLabel(packageName));
        return addMediaPlayerInfo(info);
    }

    /** Add or update a player to the media player list given the MediaPlayerInfo object.
     *  @return true if an item was updated, false if it was added instead
     */
    private boolean addMediaPlayerInfo(MediaPlayerInfo info) {
        int updateId = -1;
        boolean updated = false;
        synchronized (mMediaPlayerInfoList) {
            for (Map.Entry<Integer, MediaPlayerInfo> entry : mMediaPlayerInfoList.entrySet()) {
                if (info.getPackageName().equals(entry.getValue().getPackageName())) {
                    updateId = entry.getKey();
                    updated = true;
                    break;
                }
            }
            if (updateId == -1) {
                // New player
                mLastUsedPlayerID++;
                updateId = mLastUsedPlayerID;
            }
            mMediaPlayerInfoList.put(updateId, info);
            if (DEBUG)
                Log.d(TAG, (updated ? "update #" : "add #") + updateId + ":" + info.toString());
            if (updateId == mCurrAddrPlayerID) {
                updateCurrentController(mCurrAddrPlayerID, mCurrBrowsePlayerID);
            }
        }
        return updated;
    }

    /** Remove all players related to |packageName| from the media player info list */
    private MediaPlayerInfo removeMediaPlayerInfo(String packageName) {
        synchronized (mMediaPlayerInfoList) {
            int removeKey = -1;
            for (Map.Entry<Integer, MediaPlayerInfo> entry : mMediaPlayerInfoList.entrySet()) {
                if (entry.getValue().getPackageName().equals(packageName)) {
                    removeKey = entry.getKey();
                    break;
                }
            }
            if (removeKey != -1) {
                if (DEBUG)
                    Log.d(TAG, "remove #" + removeKey + ":" + mMediaPlayerInfoList.get(removeKey));
                return mMediaPlayerInfoList.remove(removeKey);
            }

            return null;
        }
    }

    /** Remove the controller referenced by |controller| from any player in the list */
    private void removeMediaController(@Nullable android.media.session.MediaController controller) {
        if (controller == null) return;
        synchronized (mMediaPlayerInfoList) {
            for (Map.Entry<Integer, MediaPlayerInfo> entry : mMediaPlayerInfoList.entrySet()) {
                MediaPlayerInfo info = entry.getValue();
                MediaController c = info.getMediaController();
                if (c != null && c.equals(controller)) {
                    info.setMediaController(null);
                    if (entry.getKey() == mCurrAddrPlayerID) {
                        updateCurrentController(mCurrAddrPlayerID, mCurrBrowsePlayerID);
                    }
                }
            }
        }
    }

    /*
     * utility function to get the playback state of any media player through
     * media controller APIs.
     */
    private byte getPlayStateBytes(PlaybackState pbState) {
        byte playStateBytes = PLAYSTATUS_STOPPED;

        if (pbState != null) {
            playStateBytes = (byte)convertPlayStateToBytes(pbState.getState());
            Log.v(TAG, "getPlayBackState: playStateBytes = " + playStateBytes);
        } else {
            Log.w(TAG, "playState object null, sending playStateBytes = " + playStateBytes);
        }

        return playStateBytes;
    }

    /*
     * utility function to map framework's play state values to AVRCP spec
     * defined play status values
     */
    private int convertPlayStateToBytes(int playState) {
        switch (playState) {
            case PlaybackState.STATE_PLAYING:
            case PlaybackState.STATE_BUFFERING:
                return PLAYSTATUS_PLAYING;

            case PlaybackState.STATE_STOPPED:
            case PlaybackState.STATE_NONE:
            case PlaybackState.STATE_CONNECTING:
                return PLAYSTATUS_STOPPED;

            case PlaybackState.STATE_PAUSED:
                return PLAYSTATUS_PAUSED;

            case PlaybackState.STATE_FAST_FORWARDING:
            case PlaybackState.STATE_SKIPPING_TO_NEXT:
            case PlaybackState.STATE_SKIPPING_TO_QUEUE_ITEM:
                return PLAYSTATUS_FWD_SEEK;

            case PlaybackState.STATE_REWINDING:
            case PlaybackState.STATE_SKIPPING_TO_PREVIOUS:
                return PLAYSTATUS_REV_SEEK;

            case PlaybackState.STATE_ERROR:
            default:
                return PLAYSTATUS_ERROR;
        }
    }

    /*
     * utility function to get the feature bit mask of any media player through
     * package name
     */
    private short[] getFeatureBitMask(String packageName) {

        ArrayList<Short> featureBitsList = new ArrayList<Short>();

        /* adding default feature bits */
        featureBitsList.add(AvrcpConstants.AVRC_PF_PLAY_BIT_NO);
        featureBitsList.add(AvrcpConstants.AVRC_PF_STOP_BIT_NO);
        featureBitsList.add(AvrcpConstants.AVRC_PF_PAUSE_BIT_NO);
        featureBitsList.add(AvrcpConstants.AVRC_PF_REWIND_BIT_NO);
        featureBitsList.add(AvrcpConstants.AVRC_PF_FAST_FWD_BIT_NO);
        featureBitsList.add(AvrcpConstants.AVRC_PF_FORWARD_BIT_NO);
        featureBitsList.add(AvrcpConstants.AVRC_PF_BACKWARD_BIT_NO);
        featureBitsList.add(AvrcpConstants.AVRC_PF_ADV_CTRL_BIT_NO);

        /* Add/Modify browse player supported features. */
        if (isBrowseSupported(packageName)) {
            featureBitsList.add(AvrcpConstants.AVRC_PF_BROWSE_BIT_NO);
            featureBitsList.add(AvrcpConstants.AVRC_PF_UID_UNIQUE_BIT_NO);
            featureBitsList.add(AvrcpConstants.AVRC_PF_NOW_PLAY_BIT_NO);
            featureBitsList.add(AvrcpConstants.AVRC_PF_GET_NUM_OF_ITEMS_BIT_NO);
            if (mAvrcpBipRsp != null)
                featureBitsList.add(AvrcpConstants.AVRC_PF_COVER_ART_BIT_NO);
        }

        // converting arraylist to array for response
        short[] featureBitsArray = new short[featureBitsList.size()];

        for (int i = 0; i < featureBitsList.size(); i++) {
            featureBitsArray[i] = featureBitsList.get(i).shortValue();
        }

        return featureBitsArray;
    }

    /**
     * Checks the Package name if it supports Browsing or not.
     *
     * @param packageName - name of the package to get the Id.
     * @return true if it supports browsing, else false.
     */
    private boolean isBrowseSupported(String packageName) {
        synchronized (mBrowsePlayerInfoList) {
            /* check if Browsable Player's list contains this package name */
            for (BrowsePlayerInfo info : mBrowsePlayerInfoList) {
                if (info.packageName.equals(packageName)) {
                    if (DEBUG) Log.v(TAG, "isBrowseSupported for " + packageName + ": true");
                    return true;
                }
            }
        }

        if (DEBUG) Log.v(TAG, "isBrowseSupported for " + packageName + ": false");
        return false;
    }

    private String getPackageName(int id) {
        MediaPlayerInfo player = null;
        synchronized (mMediaPlayerInfoList) {
            player = mMediaPlayerInfoList.getOrDefault(id, null);
        }

        if (player == null) {
            Log.w(TAG, "No package name for player (" + id + " not valid)");
            return "";
        }

        String packageName = player.getPackageName();
        if (DEBUG) Log.v(TAG, "Player " + id + " package: " + packageName);
        return packageName;
    }

    /* from the global object, getting the current browsed player's package name */
    private String getCurrentBrowsedPlayer(byte[] bdaddr) {
        String browsedPlayerPackage = "";

        Map<String, BrowsedMediaPlayer> connList = mAvrcpBrowseManager.getConnList();
        String bdaddrStr = new String(bdaddr);
        if(connList.containsKey(bdaddrStr)){
            browsedPlayerPackage = connList.get(bdaddrStr).getPackageName();
        }
        if (DEBUG) Log.v(TAG, "getCurrentBrowsedPlayerPackage: " + browsedPlayerPackage);
        return browsedPlayerPackage;
    }

    /* Returns the MediaPlayerInfo for the currently addressed media player */
    private MediaPlayerInfo getAddressedPlayerInfo() {
        synchronized (mMediaPlayerInfoList) {
            return mMediaPlayerInfoList.getOrDefault(mCurrAddrPlayerID, null);
        }
    }

    /*
     * Utility function to get the Media player info from package name returns
     * null if package name not found in media players list
     */
    private MediaPlayerInfo getMediaPlayerInfo(String packageName) {
        synchronized (mMediaPlayerInfoList) {
            if (mMediaPlayerInfoList.isEmpty()) {
                if (DEBUG) Log.v(TAG, "getMediaPlayerInfo: Media players list empty");
                return null;
            }

            for (MediaPlayerInfo info : mMediaPlayerInfoList.values()) {
                if (packageName.equals(info.getPackageName())) {
                    if (DEBUG) Log.v(TAG, "getMediaPlayerInfo: Found " + packageName);
                    return info;
                }
            }
            if (DEBUG) Log.w(TAG, "getMediaPlayerInfo: " + packageName + " not found");
            return null;
        }
    }

    /* prepare media list & return the media player list response object */
    private MediaPlayerListRsp prepareMediaPlayerRspObj() {
        synchronized (mMediaPlayerInfoList) {
            int numPlayers = mMediaPlayerInfoList.size();

            int[] playerIds = new int[numPlayers];
            byte[] playerTypes = new byte[numPlayers];
            int[] playerSubTypes = new int[numPlayers];
            String[] displayableNameArray = new String[numPlayers];
            byte[] playStatusValues = new byte[numPlayers];
            short[] featureBitMaskValues =
                    new short[numPlayers * AvrcpConstants.AVRC_FEATURE_MASK_SIZE];

            int players = 0;
            for (Map.Entry<Integer, MediaPlayerInfo> entry : mMediaPlayerInfoList.entrySet()) {
                MediaPlayerInfo info = entry.getValue();
                playerIds[players] = entry.getKey();
                playerTypes[players] = info.getMajorType();
                playerSubTypes[players] = info.getSubType();
                displayableNameArray[players] = info.getDisplayableName();
                playStatusValues[players] = info.getPlayStatus();

                short[] featureBits = info.getFeatureBitMask();
                for (int numBit = 0; numBit < featureBits.length; numBit++) {
                    /* gives which octet this belongs to */
                    byte octet = (byte) (featureBits[numBit] / 8);
                    /* gives the bit position within the octet */
                    byte bit = (byte) (featureBits[numBit] % 8);
                    featureBitMaskValues[(players * AvrcpConstants.AVRC_FEATURE_MASK_SIZE)
                            + octet] |= (1 << bit);
                }

                /* printLogs */
                if (DEBUG) {
                    Log.d(TAG, "Player " + playerIds[players] + ": " + displayableNameArray[players]
                                    + " type: " + playerTypes[players] + ", "
                                    + playerSubTypes[players] + " status: "
                                    + playStatusValues[players]);
                }

                players++;
            }

            if (DEBUG) Log.d(TAG, "prepareMediaPlayerRspObj: numPlayers = " + numPlayers);

            return new MediaPlayerListRsp(AvrcpConstants.RSP_NO_ERROR, sUIDCounter, numPlayers,
                    AvrcpConstants.BTRC_ITEM_PLAYER, playerIds, playerTypes, playerSubTypes,
                    playStatusValues, featureBitMaskValues, displayableNameArray);
        }
    }

     /* build media player list and send it to remote. */
    private void handleMediaPlayerListRsp(AvrcpCmd.FolderItemsCmd folderObj) {
        MediaPlayerListRsp rspObj = null;
        synchronized (mMediaPlayerInfoList) {
            int numPlayers = mMediaPlayerInfoList.size();
            if (numPlayers == 0) {
                mediaPlayerListRspNative(folderObj.mAddress, AvrcpConstants.RSP_NO_AVBL_PLAY,
                        (short) 0, (byte) 0, 0, null, null, null, null, null, null);
                return;
            }
            if (folderObj.mStartItem >= numPlayers) {
                Log.i(TAG, "handleMediaPlayerListRsp: start = " + folderObj.mStartItem
                                + " > num of items = " + numPlayers);
                mediaPlayerListRspNative(folderObj.mAddress, AvrcpConstants.RSP_INV_RANGE,
                        (short) 0, (byte) 0, 0, null, null, null, null, null, null);
                return;
            }
            rspObj = prepareMediaPlayerRspObj();
        }
        if (DEBUG) Log.d(TAG, "handleMediaPlayerListRsp: sending " + rspObj.mNumItems + " players");
        mediaPlayerListRspNative(folderObj.mAddress, rspObj.mStatus, rspObj.mUIDCounter,
                rspObj.itemType, rspObj.mNumItems, rspObj.mPlayerIds, rspObj.mPlayerTypes,
                rspObj.mPlayerSubTypes, rspObj.mPlayStatusValues, rspObj.mFeatureBitMaskValues,
                rspObj.mPlayerNameList);
    }

    /* unregister to the old controller, update new IDs and register to the new controller */
    private boolean updateCurrentController(int addrId, int browseId) {
        boolean registerRsp = true;

        updateNewIds(addrId, browseId);

        MediaController newController = null;
        MediaPlayerInfo info = getAddressedPlayerInfo();
        if (info != null) newController = info.getMediaController();

        if (DEBUG)
            Log.d(TAG, "updateCurrentController: " + mMediaController + " to " + newController);
        synchronized (this) {
            if (mMediaController == null || (!mMediaController.equals(newController))) {
                if (mMediaController != null) {
                    mMediaController.unregisterCallback(mMediaControllerCb);
                }
                mMediaController = newController;
                if (mMediaController != null) {
                    mMediaController.registerCallback(mMediaControllerCb, mHandler);
                    mAddressedMediaPlayer.updateNowPlayingList(mMediaController);
                } else {
                    mAddressedMediaPlayer.updateNowPlayingList(null);
                    registerRsp = false;
                }
            }
        }
        updateCurrentMediaState(false, null);
        return registerRsp;
    }

    /* Handle getfolderitems for scope = VFS, Search, NowPlayingList */
    private void handleGetFolderItemBrowseResponse(AvrcpCmd.FolderItemsCmd folderObj, byte[] bdaddr) {
        int status = AvrcpConstants.RSP_NO_ERROR;

        /* Browsed player is already set */
        if (folderObj.mScope == AvrcpConstants.BTRC_SCOPE_FILE_SYSTEM) {
            if (mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr) == null) {
                Log.e(TAG, "handleGetFolderItemBrowseResponse: no browsed player set for "
                                + Utils.getAddressStringFromByte(bdaddr));
                getFolderItemsRspNative(bdaddr, AvrcpConstants.RSP_INTERNAL_ERR, (short) 0,
                        (byte) 0x00, 0, null, null, null, null, null, null, null, null);
                return;
            }
            mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr).getFolderItemsVFS(folderObj);
            return;
        }
        if (folderObj.mScope == AvrcpConstants.BTRC_SCOPE_NOW_PLAYING) {
            mAddressedMediaPlayer.getFolderItemsNowPlaying(bdaddr, folderObj, mMediaController);
            return;
        }

        /* invalid scope */
        Log.e(TAG, "handleGetFolderItemBrowseResponse: unknown scope " + folderObj.mScope);
        getFolderItemsRspNative(bdaddr, AvrcpConstants.RSP_INV_SCOPE, (short) 0, (byte) 0x00, 0,
                null, null, null, null, null, null, null, null);
    }

    /* utility function to update the global values of current Addressed and browsed player */
    private void updateNewIds(int addrId, int browseId) {
        if (DEBUG)
            Log.v(TAG, "updateNewIds: Addressed:" + mCurrAddrPlayerID + " to " + addrId
                            + ", Browse:" + mCurrBrowsePlayerID + " to " + browseId);
        mCurrAddrPlayerID = addrId;
        mCurrBrowsePlayerID = browseId;
    }

    /* Getting the application's displayable name from package name */
    private String getAppLabel(String packageName) {
        ApplicationInfo appInfo = null;
        try {
            appInfo = mPackageManager.getApplicationInfo(packageName, 0);
        } catch (NameNotFoundException e) {
            e.printStackTrace();
        }

        return (String) (appInfo != null ? mPackageManager
                .getApplicationLabel(appInfo) : "Unknown");
    }

    private void handlePlayItemResponse(byte[] bdaddr, byte[] uid, byte scope) {
        if (scope == AvrcpConstants.BTRC_SCOPE_NOW_PLAYING) {
            mAddressedMediaPlayer.playItem(bdaddr, uid, mMediaController);
        }
        else {
            if(!isAddrPlayerSameAsBrowsed(bdaddr)) {
                Log.w(TAG, "Remote requesting play item on uid which may not be recognized by" +
                        "current addressed player");
                playItemRspNative(bdaddr, AvrcpConstants.RSP_INV_ITEM);
            }

            if (mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr) != null) {
                mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr).playItem(uid, scope);
            } else {
                Log.e(TAG, "handlePlayItemResponse: Remote requested playitem " +
                        "before setbrowsedplayer");
                playItemRspNative(bdaddr, AvrcpConstants.RSP_INTERNAL_ERR);
            }
        }
    }

    private void handleGetItemAttr(AvrcpCmd.ItemAttrCmd itemAttr) {
        if (itemAttr.mScope == AvrcpConstants.BTRC_SCOPE_NOW_PLAYING) {
            if (mCurrAddrPlayerID == NO_PLAYER_ID) {
                getItemAttrRspNative(
                        itemAttr.mAddress, AvrcpConstants.RSP_NO_AVBL_PLAY, (byte) 0, null, null);
                return;
            }
            mAddressedMediaPlayer.getItemAttr(itemAttr.mAddress, itemAttr, mMediaController);
            return;
        }
        // All other scopes use browsed player
        if (mAvrcpBrowseManager.getBrowsedMediaPlayer(itemAttr.mAddress) != null) {
            mAvrcpBrowseManager.getBrowsedMediaPlayer(itemAttr.mAddress).getItemAttr(itemAttr);
        } else {
            Log.e(TAG, "Could not get attributes. mBrowsedMediaPlayer is null");
            getItemAttrRspNative(
                    itemAttr.mAddress, AvrcpConstants.RSP_INTERNAL_ERR, (byte) 0, null, null);
        }
    }

    private void handleGetTotalNumOfItemsResponse(byte[] bdaddr, byte scope) {
        // for scope as media player list
        if (scope == AvrcpConstants.BTRC_SCOPE_PLAYER_LIST) {
            int numPlayers = 0;
            synchronized (mMediaPlayerInfoList) {
                numPlayers = mMediaPlayerInfoList.size();
            }
            if (DEBUG) Log.d(TAG, "handleGetTotalNumOfItemsResponse: " + numPlayers + " players.");
            getTotalNumOfItemsRspNative(bdaddr, AvrcpConstants.RSP_NO_ERROR, 0, numPlayers);
        } else if (scope == AvrcpConstants.BTRC_SCOPE_NOW_PLAYING) {
            mAddressedMediaPlayer.getTotalNumOfItems(bdaddr, mMediaController);
        } else {
            // for FileSystem browsing scopes as VFS, Now Playing
            if (mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr) != null) {
                mAvrcpBrowseManager.getBrowsedMediaPlayer(bdaddr).getTotalNumOfItems(scope);
            } else {
                Log.e(TAG, "Could not get Total NumOfItems. mBrowsedMediaPlayer is null");
                getTotalNumOfItemsRspNative(bdaddr, AvrcpConstants.RSP_INTERNAL_ERR, 0, 0);
            }
        }

    }

    /* check if browsed player and addressed player are same */
    private boolean isAddrPlayerSameAsBrowsed(byte[] bdaddr) {
        String browsedPlayer = getCurrentBrowsedPlayer(bdaddr);

        if (!isPackageNameValid(browsedPlayer)) {
            Log.w(TAG, "Browsed player name empty");
            return false;
        }

        MediaPlayerInfo info = getAddressedPlayerInfo();
        String packageName = (info == null) ? "<none>" : info.getPackageName();
        if (info == null || !packageName.equals(browsedPlayer)) {
            if (DEBUG) Log.d(TAG, browsedPlayer + " is not addressed player " + packageName);
            return false;
        }
        return true;
    }

    /* checks if package name is not null or empty */
    private boolean isPackageNameValid(String browsedPackage) {
        boolean isValid = (browsedPackage != null && browsedPackage.length() > 0);
        if (DEBUG) Log.d(TAG, "isPackageNameValid: browsedPackage = " + browsedPackage +
                "isValid = " + isValid);
        return isValid;
    }

    /* checks if selected addressed player is already addressed */
    private boolean isPlayerAlreadyAddressed(int selectedId) {
        // checking if selected ID is same as the current addressed player id
        boolean isAddressed = (mCurrAddrPlayerID == selectedId);
        if (DEBUG) Log.d(TAG, "isPlayerAlreadyAddressed: isAddressed = " + isAddressed);
        return isAddressed;
    }

    private byte[] getByteAddress(BluetoothDevice device) {
        return Utils.getBytesFromAddress(device.getAddress());
    }

    public void cleanupDeviceFeaturesIndex (int index) {
        Log.i(TAG,"cleanupDeviceFeaturesIndex index:" + index);
        deviceFeatures[index].mCurrentDevice = null;
        deviceFeatures[index].mCurrentPlayState = new PlaybackState.Builder().setState(PlaybackState.STATE_NONE, -1L, 0.0f).build();;
        deviceFeatures[index].mPlayStatusChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
        deviceFeatures[index].mTrackChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
        deviceFeatures[index].mPlaybackIntervalMs = 0L;
        deviceFeatures[index].mPlayPosChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
        deviceFeatures[index].mFeatures = 0;
        deviceFeatures[index].mAbsoluteVolume = -1;
        deviceFeatures[index].mLastSetVolume = -1;
        deviceFeatures[index].mLastDirection = 0;
        deviceFeatures[index].mVolCmdSetInProgress = false;
        deviceFeatures[index].mVolCmdAdjustInProgress = false;
        deviceFeatures[index].mAbsVolRetryTimes = 0;
        deviceFeatures[index].mAvailablePlayersChangedNT = AvrcpConstants.NOTIFICATION_TYPE_CHANGED;
    }

    private synchronized void onConnectionStateChanged(
            boolean rc_connected, boolean br_connected, byte[] address) {
        BluetoothDevice device = BluetoothAdapter.getDefaultAdapter().getRemoteDevice(address);
        Log.d(TAG, "onConnectionStateChanged " + rc_connected + " " + br_connected + " Addr:"
            + device);
        if (device == null) {
            Log.e(TAG, "onConnectionStateChanged Device is null");
            return;
        }

        if (rc_connected) {
            setAvrcpConnectedDevice(device);
        } else {
            setAvrcpDisconnectedDevice(device);
        }
    }

    public void dump(StringBuilder sb) {
        sb.append("AVRCP:\n");
        for (int i = 0; i < maxAvrcpConnections; i++) {
            Log.v(TAG,"for index " + i);
            ProfileService.println(sb, "mMediaAttributes: " + mMediaAttributes);
            ProfileService.println(sb, "mTransportControlFlags: " + mTransportControlFlags);
            ProfileService.println(sb, "mTracksPlayed: " + deviceFeatures[i].mTracksPlayed);
            ProfileService.println(sb, "mCurrentPlayState: " + deviceFeatures[i].mCurrentPlayState);
            ProfileService.println(sb, "mLastStateUpdate: " + mLastStateUpdate);
            ProfileService.println(sb, "mPlayStatusChangedNT: " + deviceFeatures[i].mPlayStatusChangedNT);
            ProfileService.println(sb, "mTrackChangedNT: " + deviceFeatures[i].mTrackChangedNT);
            ProfileService.println(sb, "mLastStateUpdate: " + mLastStateUpdate);
            ProfileService.println(sb, "mSongLengthMs: " + mSongLengthMs);
            ProfileService.println(sb, "mPlaybackIntervalMs: " + deviceFeatures[i].mPlaybackIntervalMs);
            ProfileService.println(sb, "mPlayPosChangedNT: " + deviceFeatures[i].mPlayPosChangedNT);
            ProfileService.println(sb, "mNextPosMs: " + deviceFeatures[i].mNextPosMs);
            ProfileService.println(sb, "mPrevPosMs: " + deviceFeatures[i].mPrevPosMs);
            ProfileService.println(sb, "mFeatures: " + deviceFeatures[i].mFeatures);
            ProfileService.println(sb, "mRemoteVolume: " + deviceFeatures[i].mRemoteVolume);
            ProfileService.println(sb, "mLastRemoteVolume: " + deviceFeatures[i].mLastRemoteVolume);
            ProfileService.println(sb, "mAbsoluteVolume: " + deviceFeatures[i].mAbsoluteVolume);
            ProfileService.println(sb, "mLastSetVolume: " + deviceFeatures[i].mLastSetVolume);
            ProfileService.println(sb, "mLastDirection: " + deviceFeatures[i].mLastDirection);
            ProfileService.println(sb, "mVolumeStep: " + mVolumeStep);
            ProfileService.println(sb, "mAudioStreamMax: " + mAudioStreamMax);
            ProfileService.println(sb, "mVolCmdSetInProgress: " + deviceFeatures[i].mVolCmdSetInProgress);
            ProfileService.println(sb, "mVolCmdAdjustInProgress: " + deviceFeatures[i].mVolCmdAdjustInProgress);
            ProfileService.println(sb, "mAbsVolRetryTimes: " + deviceFeatures[i].mAbsVolRetryTimes);
            ProfileService.println(sb, "mVolumeMapping: " + deviceFeatures[i].mVolumeMapping.toString());

        }
        synchronized (this) {
            if (mMediaController != null)
                ProfileService.println(sb, "mMediaController: "
                                + mMediaController.getWrappedInstance() + " pkg "
                                + mMediaController.getPackageName());
        }
        ProfileService.println(sb, "");
        ProfileService.println(sb, "Media Players:");
        synchronized (mMediaPlayerInfoList) {
            for (Map.Entry<Integer, MediaPlayerInfo> entry : mMediaPlayerInfoList.entrySet()) {
                int key = entry.getKey();
                ProfileService.println(sb, ((mCurrAddrPlayerID == key) ? " *#" : "  #")
                                + entry.getKey() + ": " + entry.getValue());
            }
        }

        ProfileService.println(sb, "");
        mAddressedMediaPlayer.dump(sb, mMediaController);

        ProfileService.println(sb, "");
        ProfileService.println(sb, mPassthroughDispatched + " passthrough operations: ");
        if (mPassthroughDispatched > mPassthroughLogs.size())
            ProfileService.println(sb, "  (last " + mPassthroughLogs.size() + ")");
        synchronized (mPassthroughLogs) {
            for (MediaKeyLog log : mPassthroughLogs) {
                ProfileService.println(sb, "  " + log);
            }
        }
        synchronized (mPassthroughPending) {
            for (MediaKeyLog log : mPassthroughPending) {
                ProfileService.println(sb, "  " + log);
            }
        }
    }

    public class AvrcpBrowseManager {
        Map<String, BrowsedMediaPlayer> connList = new HashMap<String, BrowsedMediaPlayer>();
        private AvrcpMediaRspInterface mMediaInterface;
        private Context mContext;

        public AvrcpBrowseManager(Context context, AvrcpMediaRspInterface mediaInterface) {
            mContext = context;
            mMediaInterface = mediaInterface;
        }

        public void cleanup() {
            Iterator entries = connList.entrySet().iterator();
            while (entries.hasNext()) {
                Map.Entry entry = (Map.Entry) entries.next();
                BrowsedMediaPlayer browsedMediaPlayer = (BrowsedMediaPlayer) entry.getValue();
                if (browsedMediaPlayer != null) {
                    browsedMediaPlayer.cleanup();
                }
            }
            // clean up the map
            connList.clear();
        }

        // get the a free media player interface based on the passed bd address
        // if the no items is found for the passed media player then it assignes a
        // available media player interface
        public BrowsedMediaPlayer getBrowsedMediaPlayer(byte[] bdaddr) {
            BrowsedMediaPlayer mediaPlayer;
            String bdaddrStr = new String(bdaddr);
            if (connList.containsKey(bdaddrStr)) {
                mediaPlayer = connList.get(bdaddrStr);
            } else {
                mediaPlayer = new BrowsedMediaPlayer(bdaddr, mContext, mMediaInterface);
                connList.put(bdaddrStr, mediaPlayer);
            }
            return mediaPlayer;
        }

        // clears the details pertaining to passed bdaddres
        public boolean clearBrowsedMediaPlayer(byte[] bdaddr) {
            String bdaddrStr = new String(bdaddr);
            if (connList.containsKey(bdaddrStr)) {
                connList.remove(bdaddrStr);
                return true;
            }
            return false;
        }

        public Map<String, BrowsedMediaPlayer> getConnList() {
            return connList;
        }

        /* Helper function to convert colon separated bdaddr to byte string */
        private byte[] hexStringToByteArray(String s) {
            int len = s.length();
            byte[] data = new byte[len / 2];
            for (int i = 0; i < len; i += 2) {
                data[i / 2] = (byte) ((Character.digit(s.charAt(i), 16) << 4)
                        + Character.digit(s.charAt(i+1), 16));
            }
            return data;
        }
    }

    /*
     * private class which handles responses from AvrcpMediaManager. Maps responses to native
     * responses. This class implements the AvrcpMediaRspInterface interface.
     */
    private class AvrcpMediaRsp implements AvrcpMediaRspInterface {
        private static final String TAG = "AvrcpMediaRsp";

        public void setAddrPlayerRsp(byte[] address, int rspStatus) {
            if (!setAddressedPlayerRspNative(address, rspStatus)) {
                Log.e(TAG, "setAddrPlayerRsp failed!");
            }
        }

        public void setBrowsedPlayerRsp(byte[] address, int rspStatus, byte depth, int numItems,
                String[] textArray) {
            if (!setBrowsedPlayerRspNative(address, rspStatus, depth, numItems, textArray)) {
                Log.e(TAG, "setBrowsedPlayerRsp failed!");
            }
        }

        public void mediaPlayerListRsp(byte[] address, int rspStatus, MediaPlayerListRsp rspObj) {
            if (rspObj != null && rspStatus == AvrcpConstants.RSP_NO_ERROR) {
                if (!mediaPlayerListRspNative(address, rspStatus, sUIDCounter, rspObj.itemType,
                            rspObj.mNumItems, rspObj.mPlayerIds, rspObj.mPlayerTypes,
                            rspObj.mPlayerSubTypes, rspObj.mPlayStatusValues,
                            rspObj.mFeatureBitMaskValues, rspObj.mPlayerNameList))
                    Log.e(TAG, "mediaPlayerListRsp failed!");
            } else {
                Log.e(TAG, "mediaPlayerListRsp: rspObj is null");
                if (!mediaPlayerListRspNative(address, rspStatus, sUIDCounter, (byte) 0x00, 0, null,
                            null, null, null, null, null))
                    Log.e(TAG, "mediaPlayerListRsp failed!");
            }
        }

        public void folderItemsRsp(byte[] address, int rspStatus, FolderItemsRsp rspObj) {
            if (rspObj != null && rspStatus == AvrcpConstants.RSP_NO_ERROR) {
                if (!getFolderItemsRspNative(address, rspStatus, sUIDCounter, rspObj.mScope,
                        rspObj.mNumItems, rspObj.mFolderTypes, rspObj.mPlayable, rspObj.mItemTypes,
                        rspObj.mItemUid, rspObj.mDisplayNames, rspObj.mAttributesNum,
                        rspObj.mAttrIds, rspObj.mAttrValues))
                    Log.e(TAG, "getFolderItemsRspNative failed!");
            } else {
                Log.e(TAG, "folderItemsRsp: rspObj is null or rspStatus is error:" + rspStatus);
                if (!getFolderItemsRspNative(address, rspStatus, sUIDCounter, (byte) 0x00, 0,
                        null, null, null, null, null, null, null, null))
                    Log.e(TAG, "getFolderItemsRspNative failed!");
            }

        }

        public void changePathRsp(byte[] address, int rspStatus, int numItems) {
            if (!changePathRspNative(address, rspStatus, numItems))
                Log.e(TAG, "changePathRspNative failed!");
        }

        public void getItemAttrRsp(byte[] address, int rspStatus, ItemAttrRsp rspObj) {
            if (rspObj != null && rspStatus == AvrcpConstants.RSP_NO_ERROR) {
                if (!getItemAttrRspNative(address, rspStatus, rspObj.mNumAttr,
                        rspObj.mAttributesIds, rspObj.mAttributesArray))
                    Log.e(TAG, "getItemAttrRspNative failed!");
            } else {
                Log.e(TAG, "getItemAttrRsp: rspObj is null or rspStatus is error:" + rspStatus);
                if (!getItemAttrRspNative(address, rspStatus, (byte) 0x00, null, null))
                    Log.e(TAG, "getItemAttrRspNative failed!");
            }
        }

        public void playItemRsp(byte[] address, int rspStatus) {
            if (!playItemRspNative(address, rspStatus)) {
                Log.e(TAG, "playItemRspNative failed!");
            }
        }

        public void getTotalNumOfItemsRsp(byte[] address, int rspStatus, int uidCounter,
                int numItems) {
            if (!getTotalNumOfItemsRspNative(address, rspStatus, sUIDCounter, numItems)) {
                Log.e(TAG, "getTotalNumOfItemsRspNative failed!");
            }
        }

        public void addrPlayerChangedRsp(int type, int playerId, int uidCounter, byte[] address) {
            if (!registerNotificationRspAddrPlayerChangedNative(type, playerId, sUIDCounter, address)) {
                Log.e(TAG, "registerNotificationRspAddrPlayerChangedNative failed!");
            }
        }

        public void avalPlayerChangedRsp(byte[] address, int type) {
            if (!registerNotificationRspAvalPlayerChangedNative(type, address)) {
                Log.e(TAG, "registerNotificationRspAvalPlayerChangedNative failed!");
            }
        }

        public void uidsChangedRsp(byte[] address, int type, int uidCounter) {
            if (!registerNotificationRspUIDsChangedNative(type, sUIDCounter, address)) {
                Log.e(TAG, "registerNotificationRspUIDsChangedNative failed!");
            }
        }

        public void nowPlayingChangedRsp(int type, byte[] address) {
            if (!registerNotificationRspNowPlayingChangedNative(type, address)) {
                Log.e(TAG, "registerNotificationRspNowPlayingChangedNative failed!");
            }
        }

        public void nowPlayingChangedRsp(int type) {
            if (!registerNotificationRspNowPlayingChangedNative(type, null)) {
                Log.e(TAG, "registerNotificationRspNowPlayingChangedNative failed!");
            }
        }

        public void trackChangedRsp(int type, byte[] uid, byte[] addr) {
            if (!registerNotificationRspTrackChangeNative(type, uid, addr)) {
                Log.e(TAG, "registerNotificationRspTrackChangeNative failed!");
            }
        }
    }

    private int getIndexForDevice(BluetoothDevice device) {
        for (int i = 0; i < maxAvrcpConnections; i++) {
            if (deviceFeatures[i].mCurrentDevice != null &&
                    deviceFeatures[i].mCurrentDevice.equals(device)) {
                Log.i(TAG,"device found at index " + i);
                return i;
            }
        }
        Log.e(TAG, "returning invalid index");
        return INVALID_DEVICE_INDEX;
    }

    /* getters for some private variables */
    public AvrcpBrowseManager getAvrcpBrowseManager() {
        return mAvrcpBrowseManager;
    }

    /* PASSTHROUGH COMMAND MANAGEMENT */

    void handlePassthroughCmd(int op, int state) {
        int code = avrcpPassthroughToKeyCode(op);
        if (code == KeyEvent.KEYCODE_UNKNOWN) {
            Log.w(TAG, "Ignoring passthrough of unknown key " + op + " state " + state);
            return;
        }
        int action = KeyEvent.ACTION_DOWN;
        if (state == AvrcpConstants.KEY_STATE_RELEASE) action = KeyEvent.ACTION_UP;
        KeyEvent event = new KeyEvent(action, code);
        if (!KeyEvent.isMediaKey(code)) {
            Log.w(TAG, "Passthrough non-media key " + op + " (code " + code + ") state " + state);
        }
        mMediaSessionManager.dispatchMediaKeyEvent(event);
        addKeyPending(event);
    }

    private int avrcpPassthroughToKeyCode(int operation) {
        switch (operation) {
            case BluetoothAvrcp.PASSTHROUGH_ID_UP:
                return KeyEvent.KEYCODE_DPAD_UP;
            case BluetoothAvrcp.PASSTHROUGH_ID_DOWN:
                return KeyEvent.KEYCODE_DPAD_DOWN;
            case BluetoothAvrcp.PASSTHROUGH_ID_LEFT:
                return KeyEvent.KEYCODE_DPAD_LEFT;
            case BluetoothAvrcp.PASSTHROUGH_ID_RIGHT:
                return KeyEvent.KEYCODE_DPAD_RIGHT;
            case BluetoothAvrcp.PASSTHROUGH_ID_RIGHT_UP:
                return KeyEvent.KEYCODE_DPAD_UP_RIGHT;
            case BluetoothAvrcp.PASSTHROUGH_ID_RIGHT_DOWN:
                return KeyEvent.KEYCODE_DPAD_DOWN_RIGHT;
            case BluetoothAvrcp.PASSTHROUGH_ID_LEFT_UP:
                return KeyEvent.KEYCODE_DPAD_UP_LEFT;
            case BluetoothAvrcp.PASSTHROUGH_ID_LEFT_DOWN:
                return KeyEvent.KEYCODE_DPAD_DOWN_LEFT;
            case BluetoothAvrcp.PASSTHROUGH_ID_0:
                return KeyEvent.KEYCODE_NUMPAD_0;
            case BluetoothAvrcp.PASSTHROUGH_ID_1:
                return KeyEvent.KEYCODE_NUMPAD_1;
            case BluetoothAvrcp.PASSTHROUGH_ID_2:
                return KeyEvent.KEYCODE_NUMPAD_2;
            case BluetoothAvrcp.PASSTHROUGH_ID_3:
                return KeyEvent.KEYCODE_NUMPAD_3;
            case BluetoothAvrcp.PASSTHROUGH_ID_4:
                return KeyEvent.KEYCODE_NUMPAD_4;
            case BluetoothAvrcp.PASSTHROUGH_ID_5:
                return KeyEvent.KEYCODE_NUMPAD_5;
            case BluetoothAvrcp.PASSTHROUGH_ID_6:
                return KeyEvent.KEYCODE_NUMPAD_6;
            case BluetoothAvrcp.PASSTHROUGH_ID_7:
                return KeyEvent.KEYCODE_NUMPAD_7;
            case BluetoothAvrcp.PASSTHROUGH_ID_8:
                return KeyEvent.KEYCODE_NUMPAD_8;
            case BluetoothAvrcp.PASSTHROUGH_ID_9:
                return KeyEvent.KEYCODE_NUMPAD_9;
            case BluetoothAvrcp.PASSTHROUGH_ID_DOT:
                return KeyEvent.KEYCODE_NUMPAD_DOT;
            case BluetoothAvrcp.PASSTHROUGH_ID_ENTER:
                return KeyEvent.KEYCODE_NUMPAD_ENTER;
            case BluetoothAvrcp.PASSTHROUGH_ID_CLEAR:
                return KeyEvent.KEYCODE_CLEAR;
            case BluetoothAvrcp.PASSTHROUGH_ID_CHAN_UP:
                return KeyEvent.KEYCODE_CHANNEL_UP;
            case BluetoothAvrcp.PASSTHROUGH_ID_CHAN_DOWN:
                return KeyEvent.KEYCODE_CHANNEL_DOWN;
            case BluetoothAvrcp.PASSTHROUGH_ID_PREV_CHAN:
                return KeyEvent.KEYCODE_LAST_CHANNEL;
            case BluetoothAvrcp.PASSTHROUGH_ID_INPUT_SEL:
                return KeyEvent.KEYCODE_TV_INPUT;
            case BluetoothAvrcp.PASSTHROUGH_ID_DISP_INFO:
                return KeyEvent.KEYCODE_INFO;
            case BluetoothAvrcp.PASSTHROUGH_ID_HELP:
                return KeyEvent.KEYCODE_HELP;
            case BluetoothAvrcp.PASSTHROUGH_ID_PAGE_UP:
                return KeyEvent.KEYCODE_PAGE_UP;
            case BluetoothAvrcp.PASSTHROUGH_ID_PAGE_DOWN:
                return KeyEvent.KEYCODE_PAGE_DOWN;
            case BluetoothAvrcp.PASSTHROUGH_ID_POWER:
                return KeyEvent.KEYCODE_POWER;
            case BluetoothAvrcp.PASSTHROUGH_ID_VOL_UP:
                return KeyEvent.KEYCODE_VOLUME_UP;
            case BluetoothAvrcp.PASSTHROUGH_ID_VOL_DOWN:
                return KeyEvent.KEYCODE_VOLUME_DOWN;
            case BluetoothAvrcp.PASSTHROUGH_ID_MUTE:
                return KeyEvent.KEYCODE_MUTE;
            case BluetoothAvrcp.PASSTHROUGH_ID_PLAY:
                return KeyEvent.KEYCODE_MEDIA_PLAY;
            case BluetoothAvrcp.PASSTHROUGH_ID_STOP:
                return KeyEvent.KEYCODE_MEDIA_STOP;
            case BluetoothAvrcp.PASSTHROUGH_ID_PAUSE:
                return KeyEvent.KEYCODE_MEDIA_PAUSE;
            case BluetoothAvrcp.PASSTHROUGH_ID_RECORD:
                return KeyEvent.KEYCODE_MEDIA_RECORD;
            case BluetoothAvrcp.PASSTHROUGH_ID_REWIND:
                return KeyEvent.KEYCODE_MEDIA_REWIND;
            case BluetoothAvrcp.PASSTHROUGH_ID_FAST_FOR:
                return KeyEvent.KEYCODE_MEDIA_FAST_FORWARD;
            case BluetoothAvrcp.PASSTHROUGH_ID_EJECT:
                return KeyEvent.KEYCODE_MEDIA_EJECT;
            case BluetoothAvrcp.PASSTHROUGH_ID_FORWARD:
                return KeyEvent.KEYCODE_MEDIA_NEXT;
            case BluetoothAvrcp.PASSTHROUGH_ID_BACKWARD:
                return KeyEvent.KEYCODE_MEDIA_PREVIOUS;
            case BluetoothAvrcp.PASSTHROUGH_ID_F1:
                return KeyEvent.KEYCODE_F1;
            case BluetoothAvrcp.PASSTHROUGH_ID_F2:
                return KeyEvent.KEYCODE_F2;
            case BluetoothAvrcp.PASSTHROUGH_ID_F3:
                return KeyEvent.KEYCODE_F3;
            case BluetoothAvrcp.PASSTHROUGH_ID_F4:
                return KeyEvent.KEYCODE_F4;
            case BluetoothAvrcp.PASSTHROUGH_ID_F5:
                return KeyEvent.KEYCODE_F5;
            // Fallthrough for all unknown key mappings
            case BluetoothAvrcp.PASSTHROUGH_ID_SELECT:
            case BluetoothAvrcp.PASSTHROUGH_ID_ROOT_MENU:
            case BluetoothAvrcp.PASSTHROUGH_ID_SETUP_MENU:
            case BluetoothAvrcp.PASSTHROUGH_ID_CONT_MENU:
            case BluetoothAvrcp.PASSTHROUGH_ID_FAV_MENU:
            case BluetoothAvrcp.PASSTHROUGH_ID_EXIT:
            case BluetoothAvrcp.PASSTHROUGH_ID_SOUND_SEL:
            case BluetoothAvrcp.PASSTHROUGH_ID_ANGLE:
            case BluetoothAvrcp.PASSTHROUGH_ID_SUBPICT:
            case BluetoothAvrcp.PASSTHROUGH_ID_VENDOR:
            default:
                return KeyEvent.KEYCODE_UNKNOWN;
        }
    }

    private void addKeyPending(KeyEvent event) {
        mPassthroughPending.add(new MediaKeyLog(System.currentTimeMillis(), event));
    }

    private void recordKeyDispatched(KeyEvent event, String packageName) {
        long time = System.currentTimeMillis();
        Log.v(TAG, "recordKeyDispatched: " + event + " dispatched to " + packageName);
        setAddressedMediaSessionPackage(packageName);
        synchronized (mPassthroughPending) {
            Iterator<MediaKeyLog> pending = mPassthroughPending.iterator();
            while (pending.hasNext()) {
                MediaKeyLog log = pending.next();
                if (log.addDispatch(time, event, packageName)) {
                    mPassthroughDispatched++;
                    mPassthroughLogs.add(log);
                    pending.remove();
                    return;
                }
            }
            Log.w(TAG, "recordKeyDispatch: can't find matching log!");
        }
    }

    private final MediaSessionManager.Callback mButtonDispatchCallback =
            new MediaSessionManager.Callback() {
                @Override
                public void onMediaKeyEventDispatched(KeyEvent event, MediaSession.Token token) {
                    // Get the package name
                    android.media.session.MediaController controller =
                            new android.media.session.MediaController(mContext, token);
                    String targetPackage = controller.getPackageName();
                    recordKeyDispatched(event, targetPackage);
                }

                @Override
                public void onMediaKeyEventDispatched(KeyEvent event, ComponentName receiver) {
                    recordKeyDispatched(event, receiver.getPackageName());
                }

                @Override
                public void onAddressedPlayerChanged(MediaSession.Token token) {
                    setActiveMediaSession(token);
                }

                @Override
                public void onAddressedPlayerChanged(ComponentName receiver) {
                    if (receiver == null) {
                        // No active sessions, and no session to revive, give up.
                        setAddressedMediaSessionPackage(null);
                        return;
                    }
                    // We can still get a passthrough which will revive this player.
                    setAddressedMediaSessionPackage(receiver.getPackageName());
                }
            };

    // Do not modify without updating the HAL bt_rc.h files.

    // match up with btrc_play_status_t enum of bt_rc.h
    final static int PLAYSTATUS_STOPPED = 0;
    final static int PLAYSTATUS_PLAYING = 1;
    final static int PLAYSTATUS_PAUSED = 2;
    final static int PLAYSTATUS_FWD_SEEK = 3;
    final static int PLAYSTATUS_REV_SEEK = 4;
    final static int PLAYSTATUS_ERROR = 255;

    // match up with btrc_media_attr_t enum of bt_rc.h
    final static int MEDIA_ATTR_TITLE = 1;
    final static int MEDIA_ATTR_ARTIST = 2;
    final static int MEDIA_ATTR_ALBUM = 3;
    final static int MEDIA_ATTR_TRACK_NUM = 4;
    final static int MEDIA_ATTR_NUM_TRACKS = 5;
    final static int MEDIA_ATTR_GENRE = 6;
    final static int MEDIA_ATTR_PLAYING_TIME = 7;

    // match up with btrc_event_id_t enum of bt_rc.h
    final static int EVT_PLAY_STATUS_CHANGED = 1;
    final static int EVT_TRACK_CHANGED = 2;
    final static int EVT_TRACK_REACHED_END = 3;
    final static int EVT_TRACK_REACHED_START = 4;
    final static int EVT_PLAY_POS_CHANGED = 5;
    final static int EVT_BATT_STATUS_CHANGED = 6;
    final static int EVT_SYSTEM_STATUS_CHANGED = 7;
    final static int EVT_APP_SETTINGS_CHANGED = 8;
    final static int EVENT_NOW_PLAYING_CONTENT_CHANGED = 9;
    final static int EVT_AVBL_PLAYERS_CHANGED = 0xa;
    final static int EVT_ADDR_PLAYER_CHANGED = 0xb;
    final static int EVENT_UIDS_CHANGED = 0x0c;

    private native static void classInitNative();
    private native void initNative(int maxConnections);
    private native void cleanupNative();
    private native boolean getPlayStatusRspNative(byte[] address, int playStatus, int songLen, int position);
    private native boolean getElementAttrRspNative(byte[] address, byte numAttr, int[] attrIds,
            String[] textArray);
    private native boolean registerNotificationRspPlayStatusNative(int type, int
            playStatus, byte[] address);
    private native boolean registerNotificationRspTrackChangeNative(int type, byte[]
            track, byte[] address);
    private native boolean registerNotificationRspPlayPosNative(int type, int
            playPos, byte[] address);
    private native boolean setVolumeNative(int volume, byte[] address);
    private native boolean sendPassThroughCommandNative(int keyCode, int keyState,
            byte[] address);
    private native boolean setAddressedPlayerRspNative(byte[] address, int rspStatus);
    private native boolean setBrowsedPlayerRspNative(byte[] address, int rspStatus, byte depth,
            int numItems, String[] textArray);
    private native boolean mediaPlayerListRspNative(byte[] address, int rsStatus, int uidCounter,
            byte item_type, int numItems, int[] playerIds, byte[] playerTypes, int[] playerSubTypes,
            byte[] playStatusValues, short[] featureBitMaskValues, String[] textArray);
    private native boolean getFolderItemsRspNative(byte[] address, int rspStatus, short uidCounter,
            byte scope, int numItems, byte[] folderTypes, byte[] playable, byte[] itemTypes,
            byte[] itemUidArray, String[] textArray, int[] AttributesNum, int[] AttributesIds,
            String[] attributesArray);
    private native boolean changePathRspNative(byte[] address, int rspStatus, int numItems);
    private native boolean getItemAttrRspNative(byte[] address, int rspStatus, byte numAttr,
            int[] attrIds, String[] textArray);
    private native boolean playItemRspNative(byte[] address, int rspStatus);
    private native boolean getTotalNumOfItemsRspNative(byte[] address, int rspStatus,
            int uidCounter, int numItems);
    private native boolean isDeviceActiveInHandOffNative(byte[] address);
    private native boolean searchRspNative(byte[] address, int rspStatus, int uidCounter,
            int numItems);
    private native boolean addToNowPlayingRspNative(byte[] address, int rspStatus);
    private native boolean registerNotificationRspAddrPlayerChangedNative(int type,
            int playerId, int uidCounter, byte[] address);
    private native boolean registerNotificationRspAvalPlayerChangedNative(int type, byte[] address);
    private native boolean registerNotificationRspUIDsChangedNative(int type, int uidCounter,
            byte[] address);
    private native boolean registerNotificationRspNowPlayingChangedNative(int type,
            byte[] address);

    public static String getImgHandleFromTitle(String title) {
        if (mAvrcpBipRsp != null && title != null)
            return mAvrcpBipRsp.getImgHandle(mAvrcpBipRsp.getAlbumName(title));
        return null;
    }
}
